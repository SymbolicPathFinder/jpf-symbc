package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.RegionMetricsVisitor;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SymbCondVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Invariants.LocalOutputInvariantVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns.RemoveEarlyReturns;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.STATIC;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static java.util.Collections.reverse;

/**
 * A class that represents a Static Region. That is a region that has been statically analyzed but has not been instantiated yet.
 */
public class StaticRegion implements Region {
    /**
     * Statement of the region.
     */
    public final Stmt staticStmt;

    /**
     * IR of the method that the StaticRegion belongs to.
     */
    public final IR ir;

    /**
     * An Environment table that holds a mapping from vars to either their stack slot position, in case of conditional regions, or to their parameter number in case of a MethodRegion.
     */
    public final Table slotParamTable;

    /**
     * An Environment table that holds the output of the region that needs to be popluated later to SPF upon successful veritesting. The output is computed as the last Phi for every stack slot.
     */
    public final Table outputTable;

    /**
     * this is the last instruction where SPF needs to start from after the region
     */
    public final int endIns;

    /**
     * A boolean that indicates whether this is a conditional region,i.e, a region that begins with an if instruction, or a method region, i.e., a region that is summarizing the whole method.
     */
    public final boolean isMethodRegion;

    /**
     * An environment table that defines the input vars to the region. it defines the mapping from slot/param to var
     */
    public final Table inputTable;

    /**
     * An environment table that holds the types of local variables defined inside the region.
     */
    public final VarTypeTable varTypeTable;

    /**
    * Holds the total number of IfThenElseStmts present in this static region
     */
    public int maxDepth = 0;

    /**
     * Holds the total number of execution paths that can be taken through this region
     */
    public long totalNumPaths = 0;

    /**
     * Holds the early return result that is computed by the RemoveEarlyReturns pass called in VeritestingListener
     */
    public RemoveEarlyReturns.ReturnResult earlyReturnResult;

    /**
     * Holds the expression that should be written out to the stack
     */
    public WalaVarExpr stackOutput = null;

    /**
     * @param staticStmt:     Ranger IR statement that summarizes this static region
     * @param ir:             Wala IR for the method which contains this StaticRegion
     * @param isMethodRegion: boolean value that if true indicates that this StaticRegion is for a method summary
     * @param endIns:         Ending instruction's bytecode offset for this static region
     * @param startingBlock:  if given, startingBlock is used for constructing definitions for variables used in the
     *                        condition of the staticStmt, if the StaticRegion is for a multi-path region.
     *                        startingBlock should correspond to the beginning block of the region.
     *                        If unavailable, it can be given a null value.
     * @throws StaticRegionException
     */
    public StaticRegion(Stmt staticStmt, IR ir, Boolean isMethodRegion, int endIns, ISSABasicBlock startingBlock, ISSABasicBlock terminus, RemoveEarlyReturns.ReturnResult returnResult) throws StaticRegionException {

        this.ir = ir;
        this.isMethodRegion = isMethodRegion;

        //Auxiliary vars to determine boundaries of different tables.
        Integer firstUse;
        Integer lastUse;
        Integer firstDef = null;
        Integer lastDef = null;
        Integer lastVar;
        if (returnResult == null) {
            RemoveEarlyReturns o = new RemoveEarlyReturns();
            this.earlyReturnResult = o.new ReturnResult(staticStmt);
        } else
            this.earlyReturnResult = returnResult;

        if (isMethodRegion) {
            slotParamTable = new SlotParamTable(ir, isMethodRegion, staticStmt);
            varTypeTable = new VarTypeTable(ir);
        } else {
            slotParamTable = new SlotParamTable(ir, isMethodRegion, staticStmt, new Pair<>(-2147483647, 2147483646), startingBlock.getNumber(), terminus.getNumber());
            HashSet<WalaVarExpr> noStackSlotVars = SymbCondVisitor.execute(ir, (SlotParamTable) slotParamTable, staticStmt);
            /*if (staticStmt instanceof CompositionStmt && ((CompositionStmt) staticStmt).s1 instanceof IfThenElseStmt) {
                eva.accept(((IfThenElseStmt) ((CompositionStmt) staticStmt).s1).condition);
            } else if (staticStmt instanceof CompositionStmt && ((CompositionStmt) staticStmt).s2 instanceof IfThenElseStmt) {
                eva.accept(((IfThenElseStmt) ((CompositionStmt) staticStmt).s2).condition);
            } else if (staticStmt instanceof IfThenElseStmt) {
                eva.accept(((IfThenElseStmt) staticStmt).condition);
            }*/
            if (noStackSlotVars.size() > 0) {
                StaticRegionException sre = new StaticRegionException("region contains condition that cannot be instantiated");
                SSACFG cfg = ir.getControlFlowGraph();
                if (startingBlock == null) throwException(sre, STATIC);
                ISSABasicBlock bb = startingBlock;
                boolean foundStoppingInsn = false;
                while (noStackSlotVars.size() > 0 && !foundStoppingInsn) {
                    List<SSAInstruction> bbInsns = ((SSACFG.BasicBlock) bb).getAllInstructions();
                    reverse(bbInsns);
                    for (SSAInstruction ins : bbInsns) {
                        SSAToStatDefVisitor visitor =
                                new SSAToStatDefVisitor(ir, noStackSlotVars, (SlotParamTable) slotParamTable);
                        Stmt stmt = visitor.convert(ins);
                        foundStoppingInsn = visitor.foundStoppingInsn;
                        if (stmt != null) {
                            staticStmt = new CompositionStmt(stmt, staticStmt);
                        }
                    }
                    Iterator itr = cfg.getPredNodes(bb);
                    if (cfg.getPredNodeCount(bb) != 1) foundStoppingInsn = true;
                    else bb = (ISSABasicBlock) itr.next();
                }
                if (noStackSlotVars.size() > 0) {
                    throwException(sre, STATIC);
                }
            }
//            Pair<Pair<Integer, Integer>, Pair<Integer, Integer>> regionBoundary = computeRegionBoundary(staticStmt);
            RegionBoundaryOutput regionBoundary = computeRegionBoundary(staticStmt);
            // first use var that hasn't been defined in the region, an invariant that this must be the first use in the if condition

            firstUse = regionBoundary.getFirstUse();
            lastUse = regionBoundary.getLastUse();
            firstDef = regionBoundary.getFirstDef();
            lastDef = regionBoundary.getLastDef();

            lastVar = findLastVar(firstDef, firstUse, lastDef, lastUse);
            ((SlotParamTable) slotParamTable).filterTable(new Pair<>(firstUse, lastVar), regionBoundary.getAllDefs(), regionBoundary.getAllUses());
            varTypeTable = new VarTypeTable(ir, new Pair<>(firstUse, lastVar));
        }
        this.staticStmt = staticStmt;

        inputTable = new InputTable(ir, isMethodRegion, (SlotParamTable) slotParamTable, staticStmt);


        if (isMethodRegion) //no output in terms of slots can be defined for the method region, last statement is always a return and is used to conjunct it with the outer region.
            //outputTable = new OutputTable(ir, isMethodRegion, slotParamTable, inputTable, staticStmt);
            outputTable = new OutputTable(isMethodRegion);
        else {
            if (firstDef == null) //region has no def, so no output can be defined
                outputTable = new OutputTable(isMethodRegion);
            else
                outputTable = new OutputTable(ir, isMethodRegion, (SlotParamTable) slotParamTable, (InputTable) inputTable, staticStmt, new Pair<>(firstDef, lastDef));
        }

        LocalOutputInvariantVisitor.execute(this);
        if (!isMethodRegion &&
                ((SSACFG.BasicBlock)terminus).getStackSlotPhis() != null &&
                ((SSACFG.BasicBlock)terminus).getStackSlotPhis().length != 0) {
            // a StackSlotPhi is essentially a phi instruction that computes an output that is to be written to the
            // stack and not a local variable
            SSAPhiInstruction[] stackSlotPhis = ((SSACFG.BasicBlock)terminus).getStackSlotPhis();
            if (stackSlotPhis.length != 1)
                throwException(new StaticRegionException("static regions with more than one stack output are currently unsupported"), STATIC);
            int walaStackOutputNum = stackSlotPhis[0].getDef();
            if (stackOutput != null && walaStackOutputNum != stackOutput.number)
                throwException(new StaticRegionException("Wala's stack output Wala var does not match our stack output Wala var"), STATIC);
            if (stackOutput == null) {
                if (((OutputTable) outputTable).isOutputVar(walaStackOutputNum)) {
                    // if a region summary includes a stack output, then don't consider it a local variable output
                    // since the region should be ending on an instruction that stores this stack output to the stack
                    stackOutput = new WalaVarExpr(walaStackOutputNum);
                    int[] slots = ((SlotParamTable) slotParamTable).lookup(walaStackOutputNum);
                    for (int i = 0; i < slots.length; i++)
                        outputTable.remove(slots[i]);
                }
            }
        }
        this.endIns = endIns;
        RegionMetricsVisitor.execute(this);
    }

    private Integer findLastVar(Integer firstDef, Integer firstUse, Integer lastDef, Integer lastUse) {
        ArrayList<Integer> vars = new ArrayList();
        if (firstDef != null)
            vars.add(firstDef);
        if (lastDef != null)
            vars.add(lastDef);
        if (firstUse != null)
            vars.add(firstUse);
        if (lastUse != null)
            vars.add(lastUse);

        return Collections.max(vars);
    }

    /**
     * This computes the region boundary in case of conditional region, to determine the first use and the first and last def variables inside the region.
     *
     * @param stmt Statement of the region.
     * @return A pair of pairs, ( (first-use, last-use), (first-def, last-def) ) variables in the region.
     */
    private RegionBoundaryOutput computeRegionBoundary(Stmt stmt) {
        ExprBoundaryVisitor exprBoundaryVisitor = new ExprBoundaryVisitor();

        RegionBoundaryVisitor regionBoundaryVisitor = new RegionBoundaryVisitor(exprBoundaryVisitor);
        stmt.accept(regionBoundaryVisitor);
        return regionBoundaryVisitor.getOutput();
//        return new Pair<>(new Pair<>(regionBoundaryVisitor.getFirstUse(), regionBoundaryVisitor.getLastUse()),
//                new Pair<>(regionBoundaryVisitor.getFirstDef(), regionBoundaryVisitor.getLastDef()));
    }


    public StaticRegion(Stmt staticStmt, StaticRegion staticRegion, RemoveEarlyReturns.ReturnResult returnResult) throws StaticRegionException {
        this.ir = staticRegion.ir;
        this.inputTable = staticRegion.inputTable;
        this.outputTable = staticRegion.outputTable;
        this.slotParamTable = staticRegion.slotParamTable;
        this.staticStmt = staticStmt;
        this.endIns = staticRegion.endIns;
        this.isMethodRegion = staticRegion.isMethodRegion;
        this.varTypeTable = staticRegion.varTypeTable;
        this.stackOutput = staticRegion.stackOutput;

        if (returnResult == null) {
            RemoveEarlyReturns o = new RemoveEarlyReturns();
            this.earlyReturnResult = o.new ReturnResult(staticStmt);
        } else
            this.earlyReturnResult = returnResult;
    }

}

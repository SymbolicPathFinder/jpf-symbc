package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.shrikeBT.IComparisonInstruction;
import com.ibm.wala.shrikeBT.IShiftInstruction;
import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.PhiCondition;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.PhiEdge;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil;
import org.apache.bcel.classfile.Utility;
import za.ac.sun.cs.green.expr.*;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.STATIC;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil.convertWalaVar;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil.translateBinaryOp;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil.translateUnaryOp;

/**
 * This visitor translates specific Wala SSAInstructions to RangerIR.
 */


public class SSAToStatIVisitor implements SSAInstruction.IVisitor {
    /**
     * A translated RangerIR statement.
     */
    public Stmt veriStatement;

    /**
     * Used to indicate instructions that cannot be veritested.
     */
    public boolean canVeritest = true;

    /**
     * IR of the region currently being translated to RangerIR Statement.
     */
    private IR ir;

    /**
     * A map that maps a PhiEdge with a list of all conditions that describe the path needs to be taken in the cfg to get to that edge of the phi.
     */
    private Map<PhiEdge, List<PhiCondition>> blockConditionMap;

    /**
     * Corresponds to the current condition during walking the CFG.
     */
    private Deque<PhiCondition> currentCondition;

    /**
     * current block where the instruction lies.
     */
    private ISSABasicBlock currentBlock;

    /**
     * Used to throw Static Region Exception.
     */
    private StaticRegionException pending = null;

    public SSAToStatIVisitor(IR ir,
                             ISSABasicBlock currentBlock,
                             Map<PhiEdge, List<PhiCondition>> blockConditionMap,
                             Deque<PhiCondition> currentCondition) {
        this.ir = ir;
        this.currentBlock = currentBlock;
        this.blockConditionMap = blockConditionMap;
        this.currentCondition = currentCondition;

    }

/*
    Beginning of methods for translating Phi instructions...
 */

/*
        If we want to convert constants to values eagerly, we can add this code back in.
        However, I don't think it is necessary.

       SymbolTable symtab = ir.getSymbolTable();

        if (symtab.isConstant(ssaVar)) {
            Object val = symtab.getConstantValue(ssaVar);
            if (val instanceof Boolean) {
                return new IntConstant(val.equals(Boolean.TRUE) ? 1 : 0);
            } else if (val instanceof Integer) {
                return new IntConstant((Integer)val);
            } else if (val instanceof Double) {
                return new RealConstant((Double)val);
            } else if (val instanceof String) {
                return new StringConstantGreen((String)val);
            } else {
                throwException(new StaticRegionException("translateTruncatedFinalBlock: unsupported constant type"));
                return null;
            }
        } else {
*/


    private Expression conjunct(List<Expression> le) {
        if (le.size() == 0) {
            return Operation.TRUE;
        }
        Expression result = le.get(0);
        for (int i = 1; i < le.size(); i++) {
            result = new Operation(Operation.Operator.AND, result, le.get(i));
        }
        return result;
    }

    private Expression getAndCheckCondition(List<LinkedList<PhiCondition>> conds) {
        Expression cond = conds.get(0).getFirst().condition;
        for (int i = 1; i < conds.size(); i++) {
            if (conds.get(i).getFirst().condition != cond) {
                throwException(new IllegalArgumentException("Error in getAndCheckCondition: conditions did not match!!!"), STATIC);
            }
        }
        return cond;
    }

    /**
     * Creates Gamma Expression by visiting corresponding Phi
     *
     */
    private Expression createGamma(List<LinkedList<PhiCondition>> conds, List<Expression> values) throws StaticRegionException {

        //assert(!conds.isEmpty());
        if(conds.isEmpty())
            throwException(sre, STATIC);

        // Handle leaf-level assignment
        if (conds.get(0).isEmpty()) {
            if (conds.size() != 1) throwException(sre, STATIC);
            return values.get(0);
        }

        // Handle if/then:
        // Separate 'then' and 'else' branches.
        List<LinkedList<PhiCondition>> thenConds = new ArrayList<>();
        List<LinkedList<PhiCondition>> elseConds = new ArrayList<>();
        List<Expression> thenValues = new ArrayList<>();
        List<Expression> elseValues = new ArrayList<>();

        Expression cond = getAndCheckCondition(conds);

        // NB: this code modifies the linked list as it runs.
        for (int i = 0; i < conds.size(); i++) {
            LinkedList<PhiCondition> phiConditions = conds.get(i);
            PhiCondition first = phiConditions.removeFirst();
            if (first.branch == PhiCondition.Branch.Then) {
                thenConds.add(phiConditions);
                thenValues.add(values.get(i));
            } else {
                elseConds.add(phiConditions);
                elseValues.add(values.get(i));
            }
        }

        return new GammaVarExpr(cond,
                createGamma(thenConds, thenValues),
                createGamma(elseConds, elseValues));
    }



    /**
     * Used to ignore the "out of scope" conditions corresponding to ancestor branches, if this is a phi is for a nested if/then/else,
     * @param conds Current out of scope conditions.
     */
    public void adjustForDepth(List<LinkedList<PhiCondition>> conds) {
        int depth = this.currentCondition.size();
        for (LinkedList<PhiCondition> cond : conds) {
            for (int j=0; j < depth; j++) {
                cond.removeFirst();
            }
        }
    }

    /**
     * Translates a phi to RangerIR assignment statement of a Gamma expression.
     * @param ssaphi Current PhiInstruction to be translated.
     * @return A RangerIR assignment statement to a Gamma expression
     * @throws StaticRegionException An exception that indicates that something went wrong during translation.
     */
    public Stmt translatePhi(SSAPhiInstruction ssaphi) throws StaticRegionException {
        SSACFG cfg = ir.getControlFlowGraph();
        SymbolTable symtab = ir.getSymbolTable();
        Collection<ISSABasicBlock> preds = cfg.getNormalPredecessors(currentBlock);
        Iterator<ISSABasicBlock> it = preds.iterator();
        if (ssaphi.getNumberOfUses() != preds.size()) {
            throwException(new StaticRegionException("translateTruncatedFinalBlock: normal predecessors size does not match number of phi branches"), STATIC);
            return null;
        }
        else {
            List<LinkedList<PhiCondition>> conds = new ArrayList<LinkedList<PhiCondition>>();
            List<Expression> values = new ArrayList<>();

            for (int i = 0; i < ssaphi.getNumberOfUses(); i++) {
                int ssaVar = ssaphi.getUse(i);
                ISSABasicBlock preBlock = it.next();

                List<PhiCondition> cond = blockConditionMap.get(new PhiEdge(preBlock, currentBlock));
                if (cond == null) {
                    System.out.println("Unable to find condition.");
                    SSAUtil.printBlocksUpTo(cfg, currentBlock.getNumber());
                    // MWW: null case.  Do not add to the gamma.
                    // MWW: This case occurs due to jumps from complex 'if' conditions.
                    // MWW: the top one of them will be in the blockConditionMap, but subsequent ones
                    // MWW: will not be placed in the map.
                }
                else {
                    conds.add(new LinkedList<PhiCondition>(cond));
                    values.add(convertWalaVar(ir, ssaVar));
                }
            }
            // create Gamma statement
            adjustForDepth(conds);
            return new AssignmentStmt(new WalaVarExpr(ssaphi.getDef()), createGamma(conds, values));
        }
    }

    /*
        End of Phi translating methods.
     */

    /**
     * Goto instructions are not translated to RangerIR and therefore should not be visited by this visitor.
     * @param ssaGotoInstruction
     */
    @Override
    public void visitGoto(SSAGotoInstruction ssaGotoInstruction) {
        throwException(new IllegalArgumentException("Goto seen in SSAToStatIVisitor.  This should not occur."), STATIC);
    }

    /**
     * Create an ArrayLoad Instruction in RangerIR.
     * @param ssaArrayLoadInstruction Wala SSA instruction for ArrayLoad
     */
    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction ssaArrayLoadInstruction) {
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLoadInstruction(ssaArrayLoadInstruction);
    }

    /**
     * Create an ArrayStore Instruction in RangerIR.
     * @param ssaArrayStoreInstruction Wala SSA instruction for ArrayStore
     */
    @Override
    public void visitArrayStore(SSAArrayStoreInstruction ssaArrayStoreInstruction) {
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayStoreInstruction(ssaArrayStoreInstruction);
    }

    /**
     * Create an Assignment Statement in RangerIR for binary operations in Wala.
     * @param ssa Wala SSA binary instruction.
     */
    @Override
    public void visitBinaryOp(SSABinaryOpInstruction ssa) {
        Expression lhs = new WalaVarExpr(ssa.getDef());
        Operation.Operator op = null;
        if (ssa.getOperator() instanceof IBinaryOpInstruction.Operator)
            op = translateBinaryOp((IBinaryOpInstruction.Operator) ssa.getOperator());
        else if (ssa.getOperator() instanceof IShiftInstruction.Operator)
            op = translateBinaryOp((IShiftInstruction.Operator) ssa.getOperator());
        else
            throwException(new IllegalArgumentException("Unknown Operator: " + op.toString() + " in translateBinaryOp"), STATIC);
        Expression op1 = convertWalaVar(ir, ssa.getUse(0));
        Expression op2 = convertWalaVar(ir, ssa.getUse(1));
        Expression rhs = new Operation(op, op1, op2);
        Stmt s = new AssignmentStmt(lhs, rhs);
        veriStatement = s;
        /*veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()),
                new Operation(
                        translateBinaryOp((IBinaryOpInstruction.Operator)ssa.getOperator()),
                        new WalaVarExpr(ssa.getUse(0)),
                        new WalaVarExpr(ssa.getUse(1))));*/
    }

    /**
     * Translates a unary instruction in Wala SSA to RangerIR assignment statement.
     * @param ssa SSA unary instruction.
     */
    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction ssa) {
        veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()),
                new Operation(
                        translateUnaryOp((IUnaryOpInstruction.Operator)ssa.getOpcode()),
                                convertWalaVar(ir, ssa.getUse(0)))
                );
    }

    /**
    * Casts in SPF involving object creation are beyond what we can support currently in Static regions,
    * else emulate the type casting between primitive types
    */
    @Override
    public void visitConversion(SSAConversionInstruction ssa) {
        if (!ssa.getFromType().isPrimitiveType() || !ssa.getToType().isPrimitiveType()) canVeritest = false;
        else {
            String fromType = Utility.signatureToString(ssa.getFromType().getName().getClassName().toString());
            String toType = Utility.signatureToString(ssa.getToType().getName().getClassName().toString());
            if (fromType.equals("int")) {
                if (toType.equals("long") ||
                        toType.equals("double") || toType.equals("float")) {
                    veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()), new WalaVarExpr(ssa.getUse(0)));
                } else if (toType.equals("byte") || toType.equals("char")) {
                    veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()),
                            new Operation(Operation.Operator.BIT_AND, new WalaVarExpr(ssa.getUse(0)), new IntConstant(255)));
                } else if (toType.equals("short")) {
                    veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()),
                            new Operation(Operation.Operator.BIT_AND, new WalaVarExpr(ssa.getUse(0)), new IntConstant(65535)));
                } else canVeritest = false;
            } else if (fromType.equals("double")) {
                if (toType.equals("long")) {
                    veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()), new WalaVarExpr(ssa.getUse(0)));
                } else if (toType.equals("float") || toType.equals("int")) {
                    veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()),
                            new Operation(Operation.Operator.BIT_AND, new WalaVarExpr(ssa.getUse(0)), new IntConstant(Integer.MAX_VALUE)));
                } else canVeritest = false;
            } else if (fromType.equals("long")) {
                if (toType.equals("double") || toType.equals("float") || toType.equals("int"))
                    veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()), new WalaVarExpr(ssa.getUse(0)));
                else canVeritest = false;
            } else if (fromType.equals("float")) {
                if (toType.equals("double") || toType.equals("int") || toType.equals("long"))
                    veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()), new WalaVarExpr(ssa.getUse(0)));
                else canVeritest = false;
            } else canVeritest = false;
        }
    }

    /**
     * Translates a comparision instruction in Wala SSA to RangerIR assignment statement.
     * @param ssa SSA comparision instruction.
     */
    @Override
    public void visitComparison(SSAComparisonInstruction ssa) {
        Expression expr;
        Expression condlhs = convertWalaVar(ir, ssa.getUse(0));
        Expression condrhs = convertWalaVar(ir, ssa.getUse(1));
        Operation.Operator condOp =
                (ssa.getOperator() == IComparisonInstruction.Operator.CMP ||
                        ssa.getOperator() == IComparisonInstruction.Operator.CMPG) ?
                        Operation.Operator.GT :
                        Operation.Operator.LT ;
        Expression rhs = new IfThenElseExpr(
                new Operation(condOp, condlhs, condrhs),
                Operation.ONE,
                new IfThenElseExpr(
                        new Operation(Operation.Operator.EQ, condlhs, condrhs),
                        Operation.ZERO,
                        new IntConstant(-1)));


        veriStatement =
                new AssignmentStmt(new WalaVarExpr(ssa.getDef()), rhs);
    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction ssa) {
        throwException(new IllegalArgumentException("Reached conditional branch in SSAToStatIVisitor: why?"), STATIC);
    }

    /**
     * RangerIR currently does not support Switch instruction.
     * @param ssaSwitchInstruction
     */
    @Override
    public void visitSwitch(SSASwitchInstruction ssaSwitchInstruction) {
        canVeritest = false;
    }

    /**
     * Creates RangerIR return instruction out of SSA return instruction.
     * @param ssaReturnInstruction
     */
    @Override
    public void visitReturn(SSAReturnInstruction ssaReturnInstruction) {
        veriStatement = new ReturnInstruction(ssaReturnInstruction);
    }

    /**
     * Creates RangerIR get instruction out of SSA get instruction.
     * @param ssaGetInstruction
     */
    @Override
    public void visitGet(SSAGetInstruction ssaGetInstruction) {
        veriStatement = new GetInstruction(ssaGetInstruction);
    }

    /**
     * Creates RangerIR put instruction out of SSA put instruction.
     * @param ssaPutInstruction
     */
    @Override
    public void visitPut(SSAPutInstruction ssaPutInstruction) {
        veriStatement = new PutInstruction(ssaPutInstruction);
    }

    /**
     * Creates RangerIR invoke instruction out of SSA invoke instruction.
     * @param ssaInvokeInstruction
     */
    @Override
    public void visitInvoke(SSAInvokeInstruction ssaInvokeInstruction) {
        veriStatement = new InvokeInstruction(ssaInvokeInstruction);
    }

    /**
     * Creates RangerIR new instruction out of SSA new instruction.
     * @param ssaNewInstruction
     */
    @Override
    public void visitNew(SSANewInstruction ssaNewInstruction) {
        veriStatement = new NewInstruction(ssaNewInstruction);
    }

    /**
     * Creates RangerIR array length instruction out of SSA array length instruction.
     * @param ssaArrayLengthInstruction
     */
    @Override
    public void visitArrayLength(SSAArrayLengthInstruction ssaArrayLengthInstruction) {
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLengthInstruction(ssaArrayLengthInstruction);
    }

    /**
     * Creates RangerIR throw instruction out of SSA throw instruction.
     * @param ssaThrowInstruction
     */
    @Override
    public void visitThrow(SSAThrowInstruction ssaThrowInstruction) {
        veriStatement = new ThrowInstruction(ssaThrowInstruction);
    }

    /**
     * RangerIR currently does not support SSAMonitor instructions.
     * @param ssaMonitorInstruction
     */
    @Override
    public void visitMonitor(SSAMonitorInstruction ssaMonitorInstruction) {
        canVeritest = false;
    }

    /**
     * Creates RangerIR check cast instruction out of SSA check cast instruction.
     * @param ssaCheckCastInstruction
     */
    @Override
    public void visitCheckCast(SSACheckCastInstruction ssaCheckCastInstruction) {
        veriStatement = new CheckCastInstruction(ssaCheckCastInstruction);
    }

    /**
     * Creates RangerIR instance of instruction out of SSA instance of instruction.
     * @param ssaInstanceofInstruction
     */
    @Override
    public void visitInstanceof(SSAInstanceofInstruction ssaInstanceofInstruction) {
        veriStatement = new InstanceOfInstruction(ssaInstanceofInstruction);
    }

    /**
     * Creates RangerIR phi instruction out of Wala's phi instruction.
     * @param ssaPhiInstruction
     */
    @Override
    public void visitPhi(SSAPhiInstruction ssaPhiInstruction) {
        try {
            veriStatement = translatePhi(ssaPhiInstruction);
        } catch (StaticRegionException sre) {
            pending = sre;
            canVeritest = false;
        }
    }

    /**
     * Ranger IR does not need to support Wala's Pi instruction.
     * @param ssaPiInstruction
     */
    @Override
    public void visitPi(SSAPiInstruction ssaPiInstruction) {
        veriStatement = SkipStmt.skip;
    }

    /**
     * RangerIR does not support getCaughtException.
     * @param ssaGetCaughtExceptionInstruction
     */
    @Override
    public void visitGetCaughtException(SSAGetCaughtExceptionInstruction ssaGetCaughtExceptionInstruction) {
        canVeritest = false;
    }

    /**
     * RangerIR does not support SSALoadMeta data instruction.
     * @param ssaLoadMetadataInstruction
     */
    @Override
    public void visitLoadMetadata(SSALoadMetadataInstruction ssaLoadMetadataInstruction) {
        canVeritest = false;
    }


    public static StaticRegionException sre = new StaticRegionException("Untranslatable instruction in SSAToStatIVisitor");


    public Stmt convert(SSAInstruction ssa) throws StaticRegionException {
        ssa.visit(this);
        if (!this.canVeritest) {
            if (pending != null) throwException(pending, STATIC);
            throwException(sre, STATIC);
            return null;
        }
        else return this.veriStatement;
    }

    /*
    public static Stmt convert(SSAInstruction ssa) throws StaticRegionException {
        SSAToStatIVisitor visitor = new SSAToStatIVisitor();
        ssa.visit(visitor);
        if (!visitor.canVeritest) { throwException(sre); return null; }
        else return visitor.veriStatement;
    }
    */
}


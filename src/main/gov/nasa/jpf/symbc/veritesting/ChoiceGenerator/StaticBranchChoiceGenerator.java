package gov.nasa.jpf.symbc.veritesting.ChoiceGenerator;

import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.symbc.bytecode.IFNONNULL;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.veritesting.Heuristics.HeuristicManager;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.RegionHitExactHeuristic;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.CreateStaticRegions;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

import static gov.nasa.jpf.symbc.VeritestingListener.VeritestingMode.SPFCASES;
import static gov.nasa.jpf.symbc.VeritestingListener.runMode;
import static gov.nasa.jpf.symbc.VeritestingListener.statisticManager;
import static gov.nasa.jpf.symbc.VeritestingListener.veritestingMode;
import static gov.nasa.jpf.symbc.veritesting.Heuristics.HeuristicManager.regionHeuristicFinished;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isPCSat;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isSatGreenExpression;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil.maybeParseConstraint;


public class StaticBranchChoiceGenerator extends StaticPCChoiceGenerator {


    public static int STATIC_CHOICE;
    public static int THEN_CHOICE;
    public static int ELSE_CHOICE;
    public static int RETURN_CHOICE;

    public static int HEURISTICS_THEN_CHOICE;
    public static int HEURISTICS_ELSE_CHOICE;


    public static boolean heuristicsCountingMode;


    public StaticBranchChoiceGenerator(DynamicRegion region, Instruction instruction) {
        super(3, region, instruction);

        STATIC_CHOICE = 0;
        THEN_CHOICE = 1;
        ELSE_CHOICE = 2;
        RETURN_CHOICE = 3;

        HEURISTICS_THEN_CHOICE = -1;
        HEURISTICS_ELSE_CHOICE = -1;

        this.heuristicsCountingMode = false;
        Kind kind = getKind(instruction);

        assert (kind == Kind.BINARYIF ||
                kind == Kind.NULLIF ||
                kind == Kind.UNARYIF);
    }

    public StaticBranchChoiceGenerator(DynamicRegion region, Instruction instruction, boolean heuristicsOn) {
        super(5, region, instruction);
        if (!heuristicsOn) {
            System.out.println("heuristics must be on to be able to use the heuristics choice generator!");
            assert false;
        }

        HEURISTICS_THEN_CHOICE = 0;
        HEURISTICS_ELSE_CHOICE = 1;
        STATIC_CHOICE = 2;
        THEN_CHOICE = 3;
        ELSE_CHOICE = 4;
        RETURN_CHOICE = 5;

        this.heuristicsCountingMode = heuristicsOn;

        Kind kind = getKind(instruction);

        assert (kind == Kind.BINARYIF ||
                kind == Kind.NULLIF ||
                kind == Kind.UNARYIF);
    }


    public Instruction execute(ThreadInfo ti, Instruction instructionToExecute, int choice) throws StaticRegionException {
        // if/else conditions.
        assert (choice == STATIC_CHOICE || choice == THEN_CHOICE || choice == ELSE_CHOICE || choice == RETURN_CHOICE || choice == HEURISTICS_THEN_CHOICE || choice == HEURISTICS_ELSE_CHOICE);

        Instruction nextInstruction = null;
        if (choice == STATIC_CHOICE) {
            System.out.println("\n=========Executing static region choice in BranchCG");
            nextInstruction = VeritestingListener.setupSPF(ti, instructionToExecute, getRegion(), STATIC_CHOICE);

            if(heuristicsCountingMode){
                MethodInfo methodInfo = instructionToExecute.getMethodInfo();
                String className = methodInfo.getClassName();
                String methodName = methodInfo.getName();
                String methodSignature = methodInfo.getSignature();
                int offset = instructionToExecute.getPosition();
                String key = CreateStaticRegions.constructRegionIdentifier(className + "." + methodName + methodSignature, offset);
                regionHeuristicFinished(key);
                heuristicsCountingMode = false;
                assert key.equals(HeuristicManager.getLastRegionKey());
                RegionHitExactHeuristic regionHitExactHeuristic = HeuristicManager.getRegionHeuristic();
                assert !regionHitExactHeuristic.getRegionStatus();
                if (region.totalNumPaths != regionHitExactHeuristic.getPathCount()) {
                    System.out.println("** warning: our estimated path count (" + region.totalNumPaths +
                            ") does not match exact path count (" + regionHitExactHeuristic.getPathCount());
                }
                regionHitExactHeuristic.setEstimatedPathCount(region.totalNumPaths);
            }


        }
        if (choice == HEURISTICS_THEN_CHOICE || choice == HEURISTICS_ELSE_CHOICE) {
            System.out.println("\n=========Executing" + (choice == HEURISTICS_THEN_CHOICE ? " then heuristics " : " else heuristics") + ".  Instruction: ");
            if (choice == HEURISTICS_THEN_CHOICE) {
                /*MethodInfo methodInfo = instructionToExecute.getMethodInfo();
                String className = methodInfo.getClassName();
                String methodName = methodInfo.getName();
                String methodSignature = methodInfo.getSignature();
                int offset = instructionToExecute.getPosition();
                String key = CreateStaticRegions.constructRegionIdentifier(className + "." + methodName + methodSignature, offset);
                if(!HeuristicManager.getRegionHeuristicStatus(key)){ //if we already counted the paths for this region, no need to recount it again.
                    ti.getVM().getSystemState().setIgnored(true);
                    return instructionToExecute;
                }*/

            }
            switch (getKind(instructionToExecute)) {
                case UNARYIF:
                    nextInstruction = executeUnaryIf(instructionToExecute, choice);
                    break;
                case BINARYIF:
                    nextInstruction = executeBinaryIf(instructionToExecute, choice);
                    break;
                case NULLIF:
                    nextInstruction = executeNullIf(instructionToExecute);
                    break;
                case OTHER:
                    throwException(new StaticRegionException("Error: Branch choice generator instantiated on non-branch instruction!"), INSTANTIATION);
            }
        }
        if (choice == THEN_CHOICE || choice == ELSE_CHOICE) {
            System.out.println("\n=========Executing" + (choice == THEN_CHOICE ? " then " : " else ") + ".  Instruction: ");
            maybeParseConstraint(getCurrentPC());
            switch (getKind(instructionToExecute)) {
                case UNARYIF:
                    nextInstruction = executeUnaryIf(instructionToExecute, choice);
                    break;
                case BINARYIF:
                    nextInstruction = executeBinaryIf(instructionToExecute, choice);
                    break;
                case NULLIF:
                    nextInstruction = executeNullIf(instructionToExecute);
                    break;
                case OTHER:
                    throwException(new StaticRegionException("Error: Branch choice generator instantiated on non-branch instruction!"), INSTANTIATION);
            }
        }
        if (choice == RETURN_CHOICE) { //early returns choice happened
            System.out.println("\n=========Executing early retrun choice in BranchCG");
            nextInstruction = VeritestingListener.setupSPF(ti, instructionToExecute, getRegion(), RETURN_CHOICE);
        }
        return nextInstruction;
    }

    /*
        So: here is what should happen.
        We have the PC constructed for choices 0, 1, and 2.
        In this case, we are in choice 1 or 2.

        We unpack the instruction, add it to the PC, and execute.
     */
    private Instruction executeBinaryIf(Instruction instruction, int choice) throws StaticRegionException {

        StackFrame sf = ti.getModifiableTopFrame();

        IntegerExpression sym_v1 = (IntegerExpression) sf.getOperandAttr(1);
        IntegerExpression sym_v2 = (IntegerExpression) sf.getOperandAttr(0);

        if ((sym_v1 == null) && (sym_v2 == null)) { // both conditions are concrete
            //System.out.println("Execute IF_ICMPEQ: The conditions are concrete");
            return instruction.execute(ti);
        } else {
            int v2 = sf.pop();
            int v1 = sf.pop();
            PathCondition pc;
            pc = this.getCurrentPC();

            assert pc != null;
            assert (choice == THEN_CHOICE || choice == ELSE_CHOICE || choice == HEURISTICS_THEN_CHOICE || choice == HEURISTICS_ELSE_CHOICE);

            if (choice == ELSE_CHOICE || choice == HEURISTICS_ELSE_CHOICE) {
                Comparator byteCodeOp = SpfUtil.getComparator(instruction);
                if (sym_v1 != null) {
                    if (sym_v2 != null) { //both are symbolic values
                        pc._addDet(byteCodeOp, sym_v1, sym_v2);
                    } else
                        pc._addDet(byteCodeOp, sym_v1, v2);
                } else
                    pc._addDet(byteCodeOp, v1, sym_v2);
                boolean isPCSat = isPCSat(pc);
                if (!isPCSat) {// not satisfiable
                    ti.getVM().getSystemState().setIgnored(true);
                } else {
                    this.setCurrentPC(pc);
                }
                return ((IfInstruction) instruction).getTarget();
            } else {
                assert (choice == THEN_CHOICE || choice == HEURISTICS_THEN_CHOICE);
                Comparator byteCodeNegOp = SpfUtil.getNegComparator(instruction);
                if (sym_v1 != null) {
                    if (sym_v2 != null) { //both are symbolic values
                        pc._addDet(byteCodeNegOp, sym_v1, sym_v2);
                    } else
                        pc._addDet(byteCodeNegOp, sym_v1, v2);
                } else
                    pc._addDet(byteCodeNegOp, v1, sym_v2);
                boolean isPCSat = isPCSat(pc);
                if (!isPCSat) {// not satisfiable
                    ti.getVM().getSystemState().setIgnored(true);
                } else {
                    this.setCurrentPC(pc);
                }
                return instruction.getNext(ti);
            }

        }
    }

    public Instruction executeNullIf(Instruction instruction) {

        StackFrame sf = ti.getModifiableTopFrame();
        Expression sym_v = (Expression) sf.getOperandAttr();
        if (sym_v == null) { // the condition is concrete
            //System.out.println("Execute IFEQ: The condition is concrete");
            return ((IFNONNULL) instruction).execute(ti);
        } else {
            sf.pop();
            return ((IfInstruction) instruction).getTarget();
        }
    }


    public Instruction executeUnaryIf(Instruction instruction, int choice) throws StaticRegionException {

        StackFrame sf = ti.getModifiableTopFrame();
        IntegerExpression sym_v = (IntegerExpression) sf.getOperandAttr();

        ti.getModifiableTopFrame().pop();
        if (sym_v == null) { // the condition is concrete
            return instruction.execute(ti);
        }
        PathCondition pc = this.getCurrentPC();
        if (choice == ELSE_CHOICE || choice == HEURISTICS_ELSE_CHOICE) {
            pc._addDet(SpfUtil.getComparator(instruction), sym_v, 0);
            boolean isPCSat = isPCSat(pc);
            if (!isPCSat) {// not satisfiable
                ti.getVM().getSystemState().setIgnored(true);
            } else {
                this.setCurrentPC(pc);
            }
            return ((IfInstruction) instruction).getTarget();
        } else {
            pc._addDet(SpfUtil.getNegComparator(instruction), sym_v, 0);
            boolean isPCSat = isPCSat(pc);
            if (!isPCSat) {// not satisfiable
                ti.getVM().getSystemState().setIgnored(true);
            } else {
                this.setCurrentPC(pc);
            }
            return instruction.getNext(ti);
        }
    }

    // 4 cases (they may be UNSAT, but that's ok):
    // 0: staticNominalNoReturn
    // 1: thenException
    // 2: elseException
    // 3: staticNominalReturn
    // NB: then and else constraints are the same (here).  We will tack on the additional
    // constraint for the 'then' and 'else' branches when we execute the choice generator.
    private PathCondition createPC(PathCondition pc, Expression regionSummary, Expression constraint) {
        PathCondition pcCopy = pc.make_copy();
        za.ac.sun.cs.green.expr.Expression copyConstraint = new Operation(Operation.Operator.AND, regionSummary, constraint);
        pcCopy._addDet(new GreenConstraint(copyConstraint));
        return pcCopy;
    }

    public void makeVeritestingCG(ThreadInfo ti, Instruction instructionToExecute, String key) throws StaticRegionException {
        assert (region.regionSummary != null);
        PathCondition pc;
        if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator)
            pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
        else {
            PCChoiceGenerator cg = ti.getVM().getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
            if (cg == null) throw new StaticRegionException("Cannot find latest PCChoiceGenerator");
            pc = cg.getCurrentPC();
        }
        if (this.heuristicsCountingMode) { //setup heuristics path conditions
            setPC(pc.make_copy(), HEURISTICS_THEN_CHOICE);
            setPC(pc.make_copy(), HEURISTICS_ELSE_CHOICE);
            Instruction endIns = VeritestingListener.advanceSpf(instructionToExecute, region, false);
            RegionHitExactHeuristic regionHitExactHeuristic = new RegionHitExactHeuristic(key, endIns, endIns.getMethodInfo() , 0);
            /*if(!HeuristicManager.addRegionExactHeuristic(regionHitExactHeuristic))
                this.heuristicsCountingMode = false;*/
            HeuristicManager.addRegionExactHeuristic(regionHitExactHeuristic);
        }

        ExprUtil.SatResult isSPFPredSat = isSatGreenExpression(region.spfPredicateSummary);
        if (region.earlyReturnResult.hasER()) {// Early Return & SPFCases
            setPC(createPC(pc, region.regionSummary,
                    (new Operation(Operation.Operator.AND,
                            new Operation(Operation.Operator.NOT, region.spfPredicateSummary),
                            new Operation(Operation.Operator.NOT, region.earlyReturnResult.condition)))), STATIC_CHOICE);
            if (isSPFPredSat != ExprUtil.SatResult.FALSE) {
                setPC(createPC(pc, region.regionSummary, region.spfPredicateSummary), THEN_CHOICE);
                setPC(createPC(pc, region.regionSummary, region.spfPredicateSummary), ELSE_CHOICE);
            } else {
                setPC(createPC(pc, Operation.FALSE, Operation.FALSE), THEN_CHOICE);
                setPC(createPC(pc, Operation.FALSE, Operation.FALSE), ELSE_CHOICE);
            }

            setPC(createPC(pc, region.regionSummary,
                    (new Operation(Operation.Operator.AND,
                            new Operation(Operation.Operator.NOT, region.spfPredicateSummary),
                            region.earlyReturnResult.condition))), RETURN_CHOICE);
        } else { // no early return or spfcases exists, then run only the static choice
            setPC(createPC(pc, region.regionSummary, new Operation(Operation.Operator.NOT, region.spfPredicateSummary)), STATIC_CHOICE);
            if (isSPFPredSat != ExprUtil.SatResult.FALSE) {
                setPC(createPC(pc, region.regionSummary, region.spfPredicateSummary), THEN_CHOICE);
                setPC(createPC(pc, region.regionSummary, region.spfPredicateSummary), ELSE_CHOICE);
            } else {
                setPC(createPC(pc, Operation.FALSE, Operation.FALSE), THEN_CHOICE);
                setPC(createPC(pc, Operation.FALSE, Operation.FALSE), ELSE_CHOICE);
            }
            setPC(createPC(pc, Operation.FALSE, Operation.FALSE), RETURN_CHOICE);

        }

    }

    public static int getNumSatChoices(DynamicRegion region) {
        int count  = 0;
        count += isSatGreenExpression(region.regionSummary) != ExprUtil.SatResult.FALSE ? 1 : 0;
        if (veritestingMode >= 4) count += region.spfCaseList.casesList.size();
        if (veritestingMode == 5) count += region.earlyReturnResult.hasER() ? 1 : 0;
        return count;
    }

    // Checks if the STATIC choice is the only one that is satisfiable using only ExprUtils.isSatGreenExpression()
    public static boolean isOnlyStaticChoiceSat(DynamicRegion region) {
        if (veritestingMode <= 3) {
            System.out.println("Static choice is the only choice that should be satisfiable in modes 2 and 3");
            assert false;
        }
        if (region.spfCaseList.casesList.size() > 0 || region.earlyReturnResult.hasER()) return false;
        else {
            if (isSatGreenExpression(region.regionSummary) == ExprUtil.SatResult.FALSE) {
                System.out.println("The region summary should not be false at this point");
                assert false;
            }
            return true;
        }
    }

}

package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.jvm.bytecode.GOTO;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVectorIncremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Incremental;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.CompositionStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

import java.io.File;

import static gov.nasa.jpf.symbc.VeritestingListener.performanceMode;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

/**
 * This class provides some utility methods for SPF.
 */
public class SpfUtil {

    private static int operandNum;

    /**
     * Returns number of operands depending on the if-bytecode instruction.
     * @param instruction"if" bytecode instruction
     * @return Number of operands.
     * @throws StaticRegionException
     */
    public static int getOperandNumber(String instruction) {
        switch (instruction) {
            case "ifeq":
            case "ifne":
            case "iflt":
            case "ifle":
            case "ifgt":
            case "ifge":
            case "ifnull":
            case "ifnonnull":
                operandNum = 1;
                break;
            case "if_icmpeq":
            case "if_icmpne":
            case "if_icmpgt":
            case "if_icmpge":
            case "if_icmple":
            case "if_icmplt":
            case "if_acmpne":
                operandNum = 2;
                break;
            default:
                operandNum = -1;
        }
        return operandNum;
    }

    /**
     * Checks if the "if" condition is symbolic based on the the operands of the "if" bytecode instruction.
     * @param ti Current ThreadInfo object
     * @param ins Current "if" bytecode instruction.
     * @return True if the operand(s) of "if" condition is symbolic and false if it was concerete.
     * @throws StaticRegionException
     */
    public static boolean isSymCond(ThreadInfo ti, Instruction ins) {
        StackFrame sf = ti.getTopFrame();
        boolean isSymCondition = false;
        SpfUtil.getOperandNumber(ins.getMnemonic());
        gov.nasa.jpf.symbc.numeric.Expression operand1, operand2;
        if (operandNum == 1) {
            operand1 = (gov.nasa.jpf.symbc.numeric.Expression)
                    sf.getOperandAttr();
            if (operand1 != null)
                isSymCondition = true;
            /*if (isSymCondition && VeritestingListener.performanceMode) {
                if (operand1 instanceof IntegerExpression) operand2 = new IntegerConstant(0);
                else if (operand1 instanceof RealExpression) operand2 = new RealConstant(0.0);
                else
                    return false; // we cannot figure this condition out
                isSymCondition = isBothSidesFeasible(ti, getComparator(ins), getNegComparator(ins), operand1,
                        operand2);
            }*/
        }
        if (operandNum == 2) {
            operand1 = (gov.nasa.jpf.symbc.numeric.Expression)
                    sf.getOperandAttr(1);
            if (operand1 != null)
                isSymCondition = true;
            operand2 = (gov.nasa.jpf.symbc.numeric.Expression)
                    sf.getOperandAttr(0);
            if (operand2 != null)
                isSymCondition = true;
            /*if (isSymCondition && VeritestingListener.performanceMode) {
                if (operand1 == null) {
                    if (operand2 instanceof IntegerExpression) operand1 = new IntegerConstant(sf.peek(1));
                    else if (operand2 instanceof RealExpression) operand1 = new RealConstant(sf.peekDouble(1));
                    else
                        return false; // we cannot figure this condition out
                } else if (operand2 == null) {
                    if (operand1 instanceof IntegerExpression) operand2 = new IntegerConstant(sf.peek(0));
                    else if (operand1 instanceof RealExpression) operand2 = new RealConstant(sf.peekDouble(0));
                    else
                        return false; // we cannot figure this condition out
                }
                isSymCondition = isBothSidesFeasible(ti, getComparator(ins), getNegComparator(ins), operand1, operand2);
            }*/
        }
        if(operandNum == -11)
            isSymCondition = false;

        return isSymCondition;
    }

    private static boolean isBothSidesFeasible(ThreadInfo ti, Comparator cmp, Comparator negCmp,
                                               gov.nasa.jpf.symbc.numeric.Expression op1, gov.nasa.jpf.symbc.numeric.Expression op2) {
        PathCondition pc;

        if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
            pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
        } else {
            pc = new PathCondition();
            pc._addDet(new GreenConstraint(Operation.TRUE));
        }
        PathCondition eqPC = pc.make_copy();
        PathCondition nePC = pc.make_copy();
        eqPC._addDet(cmp, op1, op2);
        nePC._addDet(negCmp, op1, op2);
        boolean eqSat = eqPC.simplify();
        boolean neSat = nePC.simplify();
        // both should never be unsat
        assert !((!eqSat) && (!neSat));
        return eqSat && neSat;
    }

    /**
     * Checks if the "if" condition is symbolic by visiting the condition expression of the statement of the staticRegion
     * @param ti Current ThreadInfo object
     * @param stmt Statement of the static region.
     * @return True if the operand(s) of "if" condition is symbolic and false if it was concerete.
     * @throws StaticRegionException
     */
    public static boolean isSymCond(ThreadInfo ti, Stmt stmt, SlotParamTable slotParamTable, Instruction ins)
            throws StaticRegionException {
        /*Expression condition = getFirstCond(stmt);
        SymbCondVisitor symbCondVisitor = new SymbCondVisitor(sf, slotParamTable, false);
        ExprVisitorAdapter eva = symbCondVisitor.eva;
        if (condition != null) eva.accept(condition);
        else throw new StaticRegionException("Cant veritesting a region that does not start with if condition");
        if (!symbCondVisitor.isSymCondition()) {
            boolean isSymCond = isSymCond(sf, ins);
            if (!isSymCond) return false;
            else throw new StaticRegionException("Failed to instantiate symbolic condition");
        } else return true;*/
        return isSymCond(ti, ins);

    }

    private static Expression getFirstCond(Stmt stmt) {
        if (stmt instanceof IfThenElseStmt) return ((IfThenElseStmt) stmt).condition;
        if (stmt instanceof CompositionStmt) {
            Expression cond = getFirstCond(((CompositionStmt) stmt).s1);
            if (cond != null) return cond;
            cond = getFirstCond(((CompositionStmt) stmt).s2);
            if (cond != null) return cond;
        }
        return null;
    }

    /**
     * This creates SPF constants depending on the type of the variable.
     * @param sf Current Stack Frame
     * @param variable Variable number for which we want to create the constant.
     * @param varType The type of which the constant should be created in SPF.
     * @return SPF constant expression..
     * @throws StaticRegionException
     */
    public static gov.nasa.jpf.symbc.numeric.Expression createSPFVariableForType(StackFrame sf, int variable, String varType) throws StaticRegionException {
        if (varType != null) {
            switch (varType) {
                case "double":
                case "float":
                case "long":
                    return new gov.nasa.jpf.symbc.numeric.RealConstant(variable);
                case "int":
                case "short":
                case "boolean":
                default: //considered here an object reference
                    return new IntegerConstant(variable);
            }
        } else {
            System.out.println("SPF does not know the type, type is assumed int.");
            return new IntegerConstant(variable);
        }
    }


    public static void emptyFolder(File folder) {
        File[] files = folder.listFiles();
        if(files!=null) { //some JVMs return null for empty dirs
            for(File f: files) {
                if(f.isDirectory()) {
                    emptyFolder(f);
                } else {
                    f.delete();
                }
            }
        }
    }



    public static Comparator getComparator(Instruction instruction) {
        switch (instruction.getMnemonic()) {
            case "ifeq":
            case "if_icmpeq":
                return Comparator.EQ;
            case "ifge":
            case "if_icmpge":
                return Comparator.GE;
            case "ifle":
            case "if_icmple":
                return Comparator.LE;
            case "ifgt":
            case "if_icmpgt":
                return Comparator.GT;
            case "iflt":
            case "if_icmplt":
                return Comparator.LT;
            case "ifne":
            case "if_icmpne":
                return Comparator.NE;
            default:
                System.out.println("Unknown comparator: " + instruction.getMnemonic());
                assert(false);
                return null;
        }
    }

    public static Comparator getNegComparator(Instruction instruction) {
        switch (instruction.getMnemonic()) {
            case "ifeq":
            case "if_icmpeq":
                return Comparator.NE;
            case "ifge":
            case "if_icmpge":
                return Comparator.LT;
            case "ifle":
            case "if_icmple":
                return Comparator.GT;
            case "ifgt":
            case "if_icmpgt":
                return Comparator.LE;
            case "iflt":
            case "if_icmplt":
                return Comparator.GE;
            case "ifne":
            case "if_icmpne":
                return Comparator.EQ;
            default:
                System.out.println("Unknown comparator: " + instruction.getMnemonic());
                assert(false);
                return null;
        }
    }

    // we want to allow only stores at the end of the region but skip regions that end on any other instruction that
    // consumes 1 or more stack operands
    public static boolean isStackConsumingRegionEnd(StaticRegion region, Instruction ins) throws StaticRegionException {
        int endIns = region.endIns;
        Instruction prevIns = null;
        while (ins != null && ins.getPosition() != endIns) {
            if (ins instanceof GOTO && (((GOTO) ins).getTarget().getPosition() <= endIns)) {
                prevIns = ins;
                ins = ((GOTO) ins).getTarget();
            }
            else {
                prevIns = ins;
                ins = ins.getNext(); // can potentially return null, seen in nativereturn instruction in java.lang.String.substring
            }
        }
        if (ins == null) {
            assert prevIns != null;
            throw new StaticRegionException("region end instruction cannot be found");
        }
        Instruction ret = ins;
        // this hack used to go along with a corresponding hack in VeritestingListener.advanceSpf that would advance
        // SPF beyond a store at the end of the region. These hacks aren't needed anymore but I am keeping this code
        // around until a month or two has gone by after we've stopped seeing these issues (March 13, 2019)
//        if (ret.getMnemonic().contains("store"))
//            return false;
        // https://en.wikipedia.org/wiki/Java_bytecode_instruction_listings
        int bytecode = ret.getByteCode();
        if (bytecode <= 0x2d) return false;
        if (bytecode >= 0x2e && bytecode <= 0x83) return true;
        if (bytecode == 0x84) return false;
        if (bytecode >= 0x85 && bytecode <= 0xa6) return true;
        if (bytecode >= 0xa7 && bytecode <= 0xa9) return false;
        if (bytecode >= 0xaa && bytecode <= 0xb0) return true;
        if (bytecode >= 0xb1 && bytecode <= 0xb2) return false;
        if (bytecode >= 0xb3 && bytecode <= 0xba) return true;
        if (bytecode == 0xbb) return false;
        if (bytecode >= 0xbc && bytecode <= 0xc7) return true;
        if (bytecode >= 0xc8 && bytecode <= 0xc9) return false;
        return true;
    }

    public static boolean isIncrementalSolver() {
        return SymbolicInstructionFactory.dp[0].equals("z3bitvectorinc") || SymbolicInstructionFactory.dp[0].equals("z3inc");
    }

    public static void maybeParseConstraint(PathCondition pc) throws StaticRegionException {
        if (isIncrementalSolver()) {
            ProblemGeneral pb = null;
            final String[] dp = SymbolicInstructionFactory.dp;
            if (dp[0].equalsIgnoreCase("z3inc")) {
                pb = new ProblemZ3Incremental();
            } else if (dp[0].equalsIgnoreCase("z3bitvectorinc")) {
                pb = new ProblemZ3BitVectorIncremental();
            }
            if (pb != null) {
                if (PCParser.parse(pc, pb) == null) {
                    throwException(new StaticRegionException("Couldn't send region summary to incremental solver"), INSTANTIATION);
                }
            }
            else throwException(new StaticRegionException("Unsupported solver type for veritesting"), INSTANTIATION);
        }
    }

}

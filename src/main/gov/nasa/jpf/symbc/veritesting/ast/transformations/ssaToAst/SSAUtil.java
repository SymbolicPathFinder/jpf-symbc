package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.shrikeBT.IConditionalBranchInstruction;
import com.ibm.wala.shrikeBT.IShiftInstruction;
import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import x10.wala.util.NatLoop;
import za.ac.sun.cs.green.expr.*;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.STATIC;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

/**
 * Some utility methods used during construction of the StaticRegion.
 */
public class SSAUtil {

    public static Collection<ISSABasicBlock> getNonReturnSuccessors(SSACFG cfg, ISSABasicBlock current) {
        SSAInstruction last = current.getLastInstruction();
        if (!(last instanceof SSAReturnInstruction) && !(last instanceof SSAThrowInstruction)) {
            return cfg.getNormalSuccessors(current);
        }
        else {
            return new ArrayList<>();
        }
    }

    public static PriorityQueue<ISSABasicBlock> constructSortedBlockPQ() {
        return new PriorityQueue<>((ISSABasicBlock o1, ISSABasicBlock o2)->o1.getNumber()-o2.getNumber());
    }

    public static <E> void enqueue(PriorityQueue<E> queue, E elem) {
        if (!queue.contains(elem)) {
            queue.add(elem);
        }
    }

    public static boolean isConditionalBranch(ISSABasicBlock current) {
        return current.getLastInstruction() instanceof SSAConditionalBranchInstruction;
    }

    public static SSAConditionalBranchInstruction getLastBranchInstruction(ISSABasicBlock current) {
        assert(current.getLastInstruction() instanceof SSAConditionalBranchInstruction);
        return (SSAConditionalBranchInstruction)current.getLastInstruction();
    }

    public static void printBlock(ISSABasicBlock block) {
        System.out.println("Basic block: " + block);
        for (SSAInstruction ins: block) {
            System.out.println("  Instruction: " + ins);
        }
        System.out.println("End of block: " + block);
    }

    public static void printBlocksUpTo(SSACFG cfg, int blockNum) {
        for (int i = 1; i <= blockNum; i++) {
            printBlock(cfg.getNode(i));
        }
    }

    // This is so dumb, but I don't know how to count instructions!
    // WALA is not very helpful for this; the multiple instruction
    // index values correspond to a single WALA instruction.

    public static boolean statefulBlock(ISSABasicBlock block) {
        int count = 0;
        for (SSAInstruction ins: block) {
            count++;
            if (count >= 2) return true;
        }
        return false;
    }


    public static Operation.Operator convertOperator(IConditionalBranchInstruction.Operator operator) {
        switch (operator) {
            case EQ: return Operation.Operator.EQ;
            case NE: return Operation.Operator.NE;
            case LT: return Operation.Operator.LT;
            case GE: return Operation.Operator.GE;
            case GT: return Operation.Operator.GT;
            case LE: return Operation.Operator.LE;
        }
        throwException(new IllegalArgumentException("convertOperator does not understand operator: " + operator), STATIC);
        return null;
    }

    public static Expression convertWalaVar(IR ir, int ssaVar) {
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
                // Eh...we don't know what it is.  Kick it to the next pass.
                return new WalaVarExpr(ssaVar);
            }
        } else {
            return new WalaVarExpr(ssaVar);
        }
    }

    public static Expression convertCondition(IR ir, SSAConditionalBranchInstruction cond) {
        return new Operation(
                convertOperator((IConditionalBranchInstruction.Operator)cond.getOperator()),
                convertWalaVar(ir, cond.getUse(0)),
                convertWalaVar(ir, cond.getUse(1)));
    }

    /**
     * Translate a binary operation to the appropriate Green operator.
     * @param op Wala operation
     * @return Equivalent Green operator
     */
    public static Operation.Operator translateBinaryOp(IBinaryOpInstruction.Operator op) {
        switch (op) {
            case ADD: return Operation.Operator.ADD;
            case SUB: return Operation.Operator.SUB;
            case MUL: return Operation.Operator.MUL;
            case DIV: return Operation.Operator.DIV;
            case REM: return Operation.Operator.MOD;
            case AND: return Operation.Operator.BIT_AND;
            case OR: return Operation.Operator.BIT_OR;
            case XOR: return Operation.Operator.BIT_XOR;
        }
        throwException(new IllegalArgumentException("Unknown Operator: " + op.toString() + " in translateBinaryOp"), STATIC);
        return null;
    }

    /**
     * Translate a binary shift operation to the appropriate Green operator.
     * @param op Wala operation
     * @return Equivalent Green operator
     */

    public static Operation.Operator translateBinaryOp(IShiftInstruction.Operator op) {
        switch (op) {
            case SHL:
                return Operation.Operator.SHIFTL;
            case SHR:
                return Operation.Operator.SHIFTR;
            case USHR:
                return Operation.Operator.SHIFTUR;
        }
        throwException(new IllegalArgumentException("Unknown Operator: " + op.toString() + " in translateBinaryOp"), STATIC);
        return null;
    }

    /**
     * Translates a unary operation in Wala to its corresponding Green operator.
     *
     */
    public static Operation.Operator translateUnaryOp(IUnaryOpInstruction.Operator op) {
        switch(op) {
            case NEG: return Operation.Operator.NEG;
        }
        throwException(new IllegalArgumentException("Unknown Operator: " + op.toString() + " in translateUnaryOp"), STATIC);
        return null;
    }

    /*
    * Returns true if this the basic block b is the start of a loop in loops
     */
    public static boolean isLoopStart(HashSet<NatLoop> loops, ISSABasicBlock b) {
        Iterator var1 = loops.iterator();

        while (var1.hasNext()) {
            NatLoop var3 = (NatLoop) var1.next();
            if (b == var3.getStart()) return true;
        }
        return false;
    }

}

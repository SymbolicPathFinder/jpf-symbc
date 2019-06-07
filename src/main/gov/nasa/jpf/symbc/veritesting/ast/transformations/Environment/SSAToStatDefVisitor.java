package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.shrikeBT.IComparisonInstruction;
import com.ibm.wala.shrikeBT.IShiftInstruction;
import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;

import java.util.ArrayList;
import java.util.HashSet;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.STATIC;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil.convertWalaVar;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil.translateBinaryOp;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil.translateUnaryOp;

public class SSAToStatDefVisitor implements SSAInstruction.IVisitor {

    private final HashSet<WalaVarExpr> noStackSlotVars;
    private final SlotParamTable slotParamTable;
    public boolean foundStoppingInsn = false;
    private Stmt veriStatement = null;
    private final IR ir;

    public SSAToStatDefVisitor(IR ir, HashSet<WalaVarExpr> noStackSlotVars, SlotParamTable slotParamTable) {
        this.noStackSlotVars = noStackSlotVars;
        this.ir = ir;
        this.slotParamTable = slotParamTable;
    }

    public Stmt convert(SSAInstruction ssa) {
        ssa.visit(this);
        return this.veriStatement;
    }

    private boolean extractStackSlotStmt(WalaVarExpr wve) {
        if (noStackSlotVars.contains(wve)) {
            noStackSlotVars.remove(wve);
            return true;
        } else veriStatement = null;
        return false;
    }

    private void addToNoStackSlotVars(WalaVarExpr wve) {
        if (slotParamTable.lookup(wve.number) == null) noStackSlotVars.add(wve);
    }

    @Override
    public void visitGoto(SSAGotoInstruction ssaGotoInstruction) { foundStoppingInsn = true; }

    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction ssaArrayLoadInstruction) {
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLoadInstruction(ssaArrayLoadInstruction);
        if (extractStackSlotStmt((WalaVarExpr) ((ArrayLoadInstruction) veriStatement).def)) {
            addToNoStackSlotVars((WalaVarExpr) ((ArrayLoadInstruction) veriStatement).arrayref);
            addToNoStackSlotVars((WalaVarExpr) ((ArrayLoadInstruction) veriStatement).index);
        }
    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction ssaArrayStoreInstruction) {}

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
        if (extractStackSlotStmt((WalaVarExpr) lhs)) {
            if (op1 instanceof WalaVarExpr) addToNoStackSlotVars((WalaVarExpr) op1);
            if (op2 instanceof WalaVarExpr) addToNoStackSlotVars((WalaVarExpr) op2);
        }
    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction ssa) {
        Expression op = convertWalaVar(ir, ssa.getUse(0));
        Expression lhs = new WalaVarExpr(ssa.getDef());
        veriStatement = new AssignmentStmt(lhs,
                new Operation(translateUnaryOp((IUnaryOpInstruction.Operator)ssa.getOpcode()), op));
        if (extractStackSlotStmt((WalaVarExpr) lhs)) {
            if (op instanceof WalaVarExpr) addToNoStackSlotVars((WalaVarExpr) op);
        }
    }

    @Override
    public void visitConversion(SSAConversionInstruction ssaConversionInstruction) {}

    @Override
    public void visitComparison(SSAComparisonInstruction ssa) {
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
        if (condlhs instanceof WalaVarExpr && extractStackSlotStmt((WalaVarExpr) condlhs))
            if (condrhs instanceof WalaVarExpr) addToNoStackSlotVars((WalaVarExpr) condrhs);
    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction ssaConditionalBranchInstruction) {}

    @Override
    public void visitSwitch(SSASwitchInstruction ssaSwitchInstruction) {}

    @Override
    public void visitReturn(SSAReturnInstruction ssaReturnInstruction) {}

    @Override
    public void visitGet(SSAGetInstruction ssaGetInstruction) {
        veriStatement = new GetInstruction(ssaGetInstruction);
        if (extractStackSlotStmt((WalaVarExpr) ((GetInstruction) veriStatement).def)) {
            if (!ssaGetInstruction.isStatic())
                addToNoStackSlotVars((WalaVarExpr) ((GetInstruction) veriStatement).ref);
        }
    }

    @Override
    public void visitPut(SSAPutInstruction ssaPutInstruction) {}

    @Override
    public void visitInvoke(SSAInvokeInstruction ssaInvokeInstruction) {
        /*veriStatement = new InvokeInstruction(ssaInvokeInstruction);
        for (Expression expression : ((InvokeInstruction) veriStatement).result) {
            WalaVarExpr wve = (WalaVarExpr) expression;
            if (extractStackSlotStmt(wve)) {
                for (Expression p : ((InvokeInstruction) veriStatement).params) {
                    addToNoStackSlotVars((WalaVarExpr) p);
                }
            }
        }*/
    }

    @Override
    public void visitNew(SSANewInstruction ssaNewInstruction) {}

    @Override
    public void visitArrayLength(SSAArrayLengthInstruction ssaArrayLengthInstruction) {
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLengthInstruction(ssaArrayLengthInstruction);
        if(extractStackSlotStmt((WalaVarExpr) ((ArrayLengthInstruction) veriStatement).def)) {
            addToNoStackSlotVars((WalaVarExpr) ((ArrayLengthInstruction) veriStatement).arrayref);
        }
    }

    @Override
    public void visitThrow(SSAThrowInstruction ssaThrowInstruction) {
        foundStoppingInsn=true;
    }

    @Override
    public void visitMonitor(SSAMonitorInstruction ssaMonitorInstruction) {}

    @Override
    public void visitCheckCast(SSACheckCastInstruction ssaCheckCastInstruction) {
        veriStatement = new CheckCastInstruction(ssaCheckCastInstruction);
        if(extractStackSlotStmt((WalaVarExpr) ((CheckCastInstruction) veriStatement).result))
            addToNoStackSlotVars((WalaVarExpr) ((CheckCastInstruction) veriStatement).val);
    }

    @Override
    public void visitInstanceof(SSAInstanceofInstruction ssaInstanceofInstruction) {}

    @Override
    public void visitPhi(SSAPhiInstruction ssaPhiInstruction) { foundStoppingInsn=true; }

    @Override
    public void visitPi(SSAPiInstruction ssaPiInstruction) { }

    @Override
    public void visitGetCaughtException(SSAGetCaughtExceptionInstruction ssaGetCaughtExceptionInstruction) {
        foundStoppingInsn=true;
    }

    @Override
    public void visitLoadMetadata(SSALoadMetadataInstruction ssaLoadMetadataInstruction) {}
}

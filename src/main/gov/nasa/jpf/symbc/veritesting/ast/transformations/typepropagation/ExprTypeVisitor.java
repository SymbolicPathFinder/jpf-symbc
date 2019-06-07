package gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation;

import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.Table;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.VarTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.RealConstant;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

public class ExprTypeVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {
    private DynamicTable varTypeTable;

    public String latestType = null;

    public DynamicTable getVarTypeTable() {
        return varTypeTable;
    }

    @Override
    public Expression visit(Operation operation) {
        if (operation.getArity() == 2) {
            Expression operand1 = operation.getOperand(0);
            Expression operand2 = operation.getOperand(1);

            String srcType = null;
            int dstNum = -1;
            Expression src = null, dst = null;
            // Figure out which one of operand1, operand2 is the src, and which is destination.
            // Type information can be propagated if one of operand1, operand2 is a constant or,
            // if one of operand1, operand2 is a Wala variable whose type information is known from before
            if (canPropagateTypeInfo(operand1, operand2)) {
                src = operand1; dst = operand2;
            }
            if (canPropagateTypeInfo(operand2, operand1)) {
                src = operand2; dst = operand1;
            }
            if (src != null && dst != null) {
                if (isConstant(src)) srcType = getConstantType(src);
                else srcType = (String) varTypeTable.lookup(src);
                dstNum = ((WalaVarExpr) dst).number;
                if (srcType != null && dstNum != -1) {
                    varTypeTable.add(dstNum, srcType);
                    latestType = srcType;
                }
            }
        }
        return super.visit(operation);
    }

    @Override
    public Expression visit(GammaVarExpr expr) {
        if (isConstant(expr.thenExpr)) latestType = getConstantType(expr.thenExpr);
        if (expr.thenExpr instanceof WalaVarExpr &&
                varTypeTable.lookup(((WalaVarExpr) expr.thenExpr).number) != null)
            latestType = (String)varTypeTable.lookup(expr.thenExpr);
        if (isConstant(expr.elseExpr)) latestType = getConstantType(expr.elseExpr);
        if (expr.elseExpr instanceof WalaVarExpr &&
                varTypeTable.lookup(((WalaVarExpr) expr.elseExpr).number) != null)
            latestType = (String) varTypeTable.lookup(expr.elseExpr);
        return super.visit(expr);
    }

    private boolean isConstant(Expression e) { return e instanceof IntConstant || e instanceof RealConstant; }

    private boolean canPropagateTypeInfo(Expression srcOp, Expression dstOp) {
        if (isConstant(srcOp)) {
            if (dstOp instanceof WalaVarExpr) {
                return true;
            }
        }
        if (srcOp instanceof WalaVarExpr) {
            int srcNum = ((WalaVarExpr) srcOp).number;
            if (varTypeTable.lookup(srcNum) != null) {
                if (dstOp instanceof WalaVarExpr) {
                    int dstNum = ((WalaVarExpr) dstOp).number;
                    if (varTypeTable.lookup(dstNum) == null) return true;
                    else if (!varTypeTable.lookup(srcNum).equals(varTypeTable.lookup(dstNum)))
                        throwException(new IllegalArgumentException("unequal types set for Wala vars used in a binop"), INSTANTIATION);
                }
            }
        }
        return false;

    }

    private String getConstantType(Expression op1) {
        if (op1 instanceof IntConstant) return "int";
        else if (op1 instanceof RealConstant) return "double";
        throwException(new IllegalArgumentException("trying to getConstantType for non-constant op, op = " + op1), INSTANTIATION);
        return null;
    }

    public ExprTypeVisitor(DynamicTable varTypeTable) {
        this.varTypeTable = varTypeTable;
    }
}

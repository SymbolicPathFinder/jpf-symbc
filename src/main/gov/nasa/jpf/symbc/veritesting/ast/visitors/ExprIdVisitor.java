package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;


public class ExprIdVisitor implements ExprVisitor<Expression> {
    @Override public Expression visit(IntConstant expr) {
        return expr;
    }
    @Override public Expression visit(IntVariable expr) {
        return expr;
    }
    @Override public Expression visit(Operation expr) { return expr; }
    @Override public Expression visit(RealConstant expr) {
        return expr;
    }
    @Override public Expression visit(RealVariable expr) {
        return expr;
    }
    @Override public Expression visit(StringConstantGreen expr) {
        return expr;
    }
    @Override public Expression visit(StringVariable expr) {
        return expr;
    }
    @Override public Expression visit(WalaVarExpr expr) {
        return expr;
    }
    @Override public Expression visit(AstVarExpr expr) {
        return expr;
    }
    @Override public Expression visit(FieldRefVarExpr expr) {
        return expr;
    }

    @Override
    public Expression visit(ArrayRefVarExpr expr) {
        return expr;
    }

    @Override public Expression visit(GammaVarExpr expr) { return expr; }
    @Override public Expression visit(IfThenElseExpr expr) { return expr; }
}

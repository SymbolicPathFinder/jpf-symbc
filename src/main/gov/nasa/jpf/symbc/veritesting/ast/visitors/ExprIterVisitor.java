package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;

import java.util.function.BinaryOperator;

/*
    Preconditions:
        defaultVal should be a 'zero' element for combine.  That is:
            combine(V, defaultVal) = V;
        Also, combine should be commutative and associative.
 */

/**
 * Visits all expressions and applies the checking "combine" and returns the result of the checking.
 * @param <T>
 */
public class ExprIterVisitor<T> implements ExprVisitor<T> {

    protected final BinaryOperator<T> combine;
    protected final T defaultVal;

    protected final ExprVisitorAdapter<T> eva =
            new ExprVisitorAdapter<T>(this);

    public ExprIterVisitor(BinaryOperator<T> combine, T defaultVal) {
        this.defaultVal = defaultVal;
        this.combine = combine;
    }

    @Override public T visit(IntConstant expr) {
        return defaultVal;
    }
    @Override public T visit(IntVariable expr) {
        return defaultVal;
    }

    @Override
    public T visit(Operation expr) {
        T toReturn = defaultVal;
        for (Expression e: expr.getOperands()) {
            combine.apply(toReturn, eva.accept(e));
        }
        return toReturn;
    }

    @Override public T visit(RealConstant expr) {
        return defaultVal;
    }
    @Override public T visit(RealVariable expr) {
        return defaultVal;
    }
    @Override public T visit(StringConstantGreen expr) {
        return defaultVal;
    }
    @Override public T visit(StringVariable expr) {
        return defaultVal;
    }
    @Override public T visit(WalaVarExpr expr) {
        return defaultVal;
    }
    @Override public T visit(AstVarExpr expr) {
        return defaultVal;
    }
    @Override public T visit(FieldRefVarExpr expr) {
        return defaultVal;
    }

    @Override
    public T visit(ArrayRefVarExpr expr) {
        return defaultVal;
    }

    @Override
    public T visit(GammaVarExpr expr) {
        return combine.apply(eva.accept(expr.condition),
                combine.apply(eva.accept(expr.thenExpr),
                              eva.accept(expr.elseExpr)));
    }

    @Override
    public T visit(IfThenElseExpr expr) {
        return combine.apply(eva.accept(expr.condition),
                combine.apply(eva.accept(expr.thenExpr),
                              eva.accept(expr.elseExpr)));
    }
}

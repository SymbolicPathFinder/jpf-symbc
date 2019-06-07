package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.EquationExprVisitor;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.DONTKNOW;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

/**
 * An adaptor that pushes the visitor to the right visit for a Green expression.
 * @param <T>
 */
public class ExprVisitorAdapter<T>  {

    public ExprVisitor<T> theVisitor;

    public ExprVisitorAdapter(ExprVisitor<T> theVisitor) {
        this.theVisitor = theVisitor;
    }

    public ExprVisitorAdapter(EquationExprVisitor theVisitor) {
        this.theVisitor = (ExprVisitor<T>) theVisitor;
    }

    // doing a kind of gross thing since the visitor support I like is not
    // built into Green: forcing the issue with a bunch of type tests.
    public T accept(Expression e) {
        if (e instanceof IntConstant) {
            return theVisitor.visit((IntConstant) e);
        } else if (e instanceof IntVariable) {
            return theVisitor.visit((IntVariable) e);
        } else if (e instanceof Operation) {
            return theVisitor.visit((Operation) e);
        } else if (e instanceof RealConstant) {
            return theVisitor.visit((RealConstant) e);
        } else if (e instanceof RealVariable) {
            return theVisitor.visit((RealVariable) e);
        } else if (e instanceof StringConstantGreen) {
            return theVisitor.visit((StringConstantGreen) e);
        } else if (e instanceof StringVariable) {
            return theVisitor.visit((StringVariable) e);
        } else if (e instanceof FieldRefVarExpr) {
            return theVisitor.visit((FieldRefVarExpr) e);
        } else if (e instanceof ArrayRefVarExpr) {
            return theVisitor.visit((ArrayRefVarExpr) e);
        } else if (e instanceof GammaVarExpr) {
            return theVisitor.visit((GammaVarExpr) e);
        } else if (e instanceof WalaVarExpr) {
            return theVisitor.visit((WalaVarExpr) e);
        } else if (e instanceof IfThenElseExpr) {
            return theVisitor.visit((IfThenElseExpr) e);
        } else if (e instanceof AstVarExpr) {
            return theVisitor.visit((AstVarExpr)e);
        }
        else {
            throwException(new IllegalArgumentException("Unknown class in ExprVisitorAdapter!"), DONTKNOW);
            return (T) e;
        }
    }

}

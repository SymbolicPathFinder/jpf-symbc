package gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.FieldRefTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.createGreenVar;


/**
 * A visitor that visits all FieldRefVarExpr and generates the appropriate SPF symbolic variable based on its type.
 */

public class FieldArrayVarToSPFVarVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    private final FieldRefTypeTable fieldRefTypeTable;

    protected final ExprVisitorAdapter<Expression> eva =
            new ExprVisitorAdapter<Expression>(this);

    public FieldArrayVarToSPFVarVisitor(FieldRefTypeTable fieldRefTypeTable) {
        this.fieldRefTypeTable = fieldRefTypeTable;
    }

    @Override
    public Expression visit(IfThenElseExpr expr) {
        return new IfThenElseExpr(eva.accept(expr.condition),
                eva.accept(expr.thenExpr),
                eva.accept(expr.elseExpr));
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        String type = fieldRefTypeTable.lookup(expr);
        if (type != null)
            return createGreenVar(type, expr.getSymName());
        else {
            throwException(new IllegalArgumentException("Failed to infer type of field reference, " + expr), INSTANTIATION);
            return expr;
        }
    }

    @Override
    public Expression visit(ArrayRefVarExpr expr) {
        String type = fieldRefTypeTable.lookup(expr);
        if (type != null)
            return createGreenVar(type, expr.getSymName());
        else
            throwException(new IllegalArgumentException("Failed to infer type of array reference, " + expr), INSTANTIATION);
        return expr;
    }

    @Override
    public Expression visit(WalaVarExpr expr) {
        return expr;
    }

    @Override
    public Expression visit(GammaVarExpr expr) {
        return new GammaVarExpr(eva.accept(expr.condition),
                eva.accept(expr.thenExpr),
                eva.accept(expr.elseExpr));
    }

}
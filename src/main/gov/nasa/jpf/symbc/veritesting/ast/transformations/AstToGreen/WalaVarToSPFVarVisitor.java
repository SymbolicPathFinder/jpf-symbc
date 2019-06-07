package gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.VarTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import ia_parser.Exp;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.createGreenVar;

/**
 * A visitor that visits all WalaVarExp and generate the appropriate SPF symbolic variable depending on its type.
 */

public class WalaVarToSPFVarVisitor implements ExprVisitor<Expression> {

    private final DynamicTable varTypeTable;

    protected final ExprVisitorAdapter<Expression> eva =
            new ExprVisitorAdapter<Expression>(this);

    public WalaVarToSPFVarVisitor(DynamicTable varTypeTable) {
        this.varTypeTable = varTypeTable;
    }

    @Override
    public Expression visit(IntConstant expr) {
        return expr;
    }

    @Override
    public Expression visit(IntVariable expr) {
        return expr;
    }

    @Override
    public Expression visit(Operation expr) {
        Expression[] exps = new Expression[expr.getArity()];
        for(int i = 0; i < expr.getArity(); i++){
            exps[i] = eva.accept(expr.getOperand(i));
        }
        return new Operation(expr.getOperator(), exps);    }

    @Override
    public Expression visit(RealConstant expr) {
        return expr;
    }

    @Override
    public Expression visit(RealVariable expr) {
        return expr;
    }

    @Override
    public Expression visit(StringConstantGreen expr) {
        return expr;
    }

    @Override
    public Expression visit(StringVariable expr) {
        return expr;
    }

    @Override
    public Expression visit(IfThenElseExpr expr) {
        return new IfThenElseExpr(eva.accept(expr.condition),
                eva.accept(expr.thenExpr),
                eva.accept(expr.elseExpr));
    }

    @Override
    public Expression visit(WalaVarExpr expr) {
        String type = (String) varTypeTable.lookup(expr);
        if (type != null)
            return createGreenVar(type, expr.getSymName());
        else
            throwException(new IllegalArgumentException("Failed to infer type of Wala var, " + expr), INSTANTIATION);
        return expr;
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return expr;
    }

    @Override
    public Expression visit(ArrayRefVarExpr expr) {
        return expr;
    }

    @Override
    public Expression visit(GammaVarExpr expr) {
        return new GammaVarExpr(eva.accept(expr.condition),
                eva.accept(expr.thenExpr),
                eva.accept(expr.elseExpr));
    }

    @Override
    public Expression visit(AstVarExpr expr) {
        return createGreenVar(expr.type, expr.getSymName());
    }
}
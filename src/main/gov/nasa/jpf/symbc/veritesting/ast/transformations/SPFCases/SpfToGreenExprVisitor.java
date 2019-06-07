package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.AstToGreenVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.FieldArrayVarToSPFVarVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.NoSkipVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.WalaVarToSPFVarVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.DefUseVisit;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import ia_parser.Exp;
import za.ac.sun.cs.green.expr.*;

import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

//TODO: Remove this SOHA
public class SpfToGreenExprVisitor implements ExprVisitor<Expression> {

    Expression toAssign;
    ExprVisitorAdapter<Expression> eva;

    public SpfToGreenExprVisitor() {
        this.toAssign = toAssign;
        eva = new ExprVisitorAdapter<Expression>(this);
    }


    public void setAssign(Expression toAssign) {
        this.toAssign = toAssign;
    }

    public static Expression bad(Object obj) {
        String name = obj.getClass().getCanonicalName();
        throwException(new IllegalArgumentException("Unsupported class: " + name + " value: " + obj.toString() + " seen in AstToGreenExprVisitor"), INSTANTIATION);
        return null;
    }

    public Expression assign(Expression e) {
        Expression assign = new Operation(Operation.Operator.EQ, toAssign, e);
        //return new Operation(Operation.Operator.AND, currentCondition, assign);
        return null;
    }

    @Override
    public Expression visit(GammaVarExpr expr) {
        return bad(expr);
    }

    @Override
    public Expression visit(AstVarExpr expr) { return bad(expr); }

    @Override
    public Expression visit(IfThenElseExpr expr) {
        return bad(expr);
    }

    @Override
    public Expression visit(WalaVarExpr expr) {
        return bad(expr);
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return bad(expr);
    }

    @Override
    public Expression visit(ArrayRefVarExpr expr) {
        return bad(expr);
    }

    @Override
    public Expression visit(IntConstant expr) {
        return assign(expr);
    }

    @Override
    public Expression visit(IntVariable expr) {
        return assign(expr);
    }

    @Override
    public Expression visit(Operation expr) {
        return assign(expr);
    }

    @Override
    public Expression visit(RealConstant expr) {
        return assign(expr);
    }

    @Override
    public Expression visit(RealVariable expr) {
        return assign(expr);
    }

    @Override
    public Expression visit(StringConstantGreen expr) {
        return assign(expr);
    }

    @Override
    public Expression visit(StringVariable expr) {
        return assign(expr);
    }
}

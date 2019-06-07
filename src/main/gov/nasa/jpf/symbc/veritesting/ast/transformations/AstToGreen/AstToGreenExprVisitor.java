package gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.VarTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.DefUseVisit;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.createGreenVar;

/*
    The central difficulty here is determining the condition under which to
    assign a variable underneath an IfThenElseExpr and/or Gamma expr.

    NOTE: When Green adds support for IfThenElse expressions, this will become
    unnecessary...maybe we should just add it there.

    This is also an example where supporting an argument in a visitor would be
    quite nice.  Oh well.
 */

/**
 * This is a visitor class that Translate expression in RangerIR to te appropriate Green expression.
 */

public class AstToGreenExprVisitor implements ExprVisitor<Expression> {

    Expression toAssign;
    Expression currentCondition;
    ExprVisitorAdapter<Expression> eva;
    public DefUseVisit defUseVisit;

    public AstToGreenExprVisitor() {
        this.toAssign = toAssign;
        this.currentCondition = Operation.TRUE;
        eva = new ExprVisitorAdapter<Expression>(this);
    }


//     <VBS> This setAssign mechanism is terrible. It sets up state in this visitor that gets used in the next visited
//     expression but there are no expected on the type of next visited expression. The invariant is that toAssign
//     should be used only in the next assign() call but there is no defense against
//     (1) the user of this visitor forgetting to set up toAssign
//     (2) toAssign being used in multiple assign() calls
//     I wish this visitor was written differently to avoid any prior setup of its internal state
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
        if (currentCondition.equals(Operation.TRUE)) {
            return assign;
        } else {
            return new Operation(Operation.Operator.AND, currentCondition, assign);
        }
    }

    /**
     * Translates conditional expression to a corresponding Green expression.
     *
     * @param cond     Condition inside the expression.
     * @param thenExpr Expression in the then side.
     * @param elseExpr Expression in the else side.
     * @return Green expression that represents the the IfThenElseExpression.
     */
    public Expression ite(Expression cond, Expression thenExpr, Expression elseExpr) {
        Expression prevCond = currentCondition;
        Expression thenCond = new Operation(Operation.Operator.AND, currentCondition, cond);
        Expression elseCond = new Operation(Operation.Operator.AND, currentCondition,
                new Operation(Operation.Operator.NOT, cond));
        currentCondition = thenCond;
        Expression thenBranches = eva.accept(thenExpr);
        currentCondition = elseCond;
        Expression elseBranches = eva.accept(elseExpr);
        Expression finalExpr = new Operation(Operation.Operator.OR, thenBranches, elseBranches);
        currentCondition = prevCond;
        return finalExpr;
    }

    /**
     * Translating a GammaExpression into an IfThenElseExpression
     *
     * @param expr A Gamma expression to be translated.
     * @return A IfThenElseExpr that needs to be later translated to a Green Expression.
     */
    @Override
    public Expression visit(GammaVarExpr expr) {
        return ite(expr.condition, (Expression) expr.thenExpr, (Expression) expr.elseExpr);
    }

    @Override
    public Expression visit(AstVarExpr expr) {
        return bad(expr);
    }


    /**
     * Translating a TfThenElseExpr into an IfThenElseExpression
     *
     * @param expr A Gamma expression to be translated.
     * @return A IfThenElseExpr that needs to be later translated to a Green Expression.
     */
    @Override
    public Expression visit(IfThenElseExpr expr) {
        return ite(expr.condition, expr.thenExpr, expr.elseExpr);
    }

    @Override
    public Expression visit(WalaVarExpr expr) {
        return bad(expr);
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return bad(expr);
    }

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

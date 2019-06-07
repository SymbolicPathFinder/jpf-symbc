package gov.nasa.jpf.symbc.veritesting.ast.def;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

/**
 * This is IfThenElse expression in Ranger IR
 */
public class IfThenElseExpr extends Expression {
    public final Expression condition;
    public final Expression thenExpr;
    public final Expression elseExpr;

    public IfThenElseExpr(Expression condition, Expression thenExpr, Expression elseExpr) {
        this.condition = condition;
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }


    @Override
    public void accept(Visitor visitor) throws VisitorException {
        visitor.preVisit(this);
        condition.accept(visitor);
        thenExpr.accept(visitor);
        elseExpr.accept(visitor);
        visitor.postVisit(this);
    }

    @Override
    public boolean equals(Object o) {
        return false;
    }

    @Override
    public String toString() {
        return " if (" + this.condition + ") then (" + thenExpr.toString() + ") else (" + elseExpr.toString() + ")";
    }

    @Override
    public int getLength() {
        return 0;
    }

    @Override
    public int getLeftLength() {
        return 0;
    }

    @Override
    public int numVar() {
        return 0;
    }

    @Override
    public int numVarLeft() {
        return 0;
    }

    @Override
    public List<String> getOperationVector() {
        return null;
    }
}

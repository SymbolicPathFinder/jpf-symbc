package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

/*
    MWW TODO: This class might be better represented as a list of <condition, assign> pairs
        TODO: as this is a more accurate representation of what is in the SSA form, and it
        TODO: would allow opportunities for subsequent optimization.  However, for now I
        TODO: am leaving it as it is.
 */


/**
 * This class provides the representation of Gamma in RangerIR which is extends a Phi to include the condition under which the choice is taken.
 */
public final class GammaVarExpr extends Variable {
    public final Expression condition;
    public final Expression thenExpr;
    public final Expression elseExpr;

    public GammaVarExpr(Expression condition, Expression thenExpr, Expression elseExpr) {
        super("(Gamma " + condition.toString() + " " + thenExpr.toString() + " " + elseExpr.toString() + ")");
        this.condition = condition;
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }


    @Override
    public void accept(Visitor visitor) throws VisitorException {
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    @Override
    // I am making class final so that equality works correctly.
    public boolean equals(Object o) {
        if (o != null && o instanceof GammaVarExpr) {
            GammaVarExpr other = (GammaVarExpr)o;
            return (this.condition.equals(other.condition) &&
                    this.thenExpr.equals(other.thenExpr) &&
                    this.elseExpr.equals(other.elseExpr));
        }
        return false;
    }

    @Override
    public String toString() {
        return getName();
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

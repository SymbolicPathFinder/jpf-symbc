package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is SPFCases in RangerIR. These are basically a place holder for places in RangerIR where SPF needs to explore.
 */

public class SPFCaseStmt implements Stmt {

    public final Expression spfCondition;
    public final SPFReason reason;

    /**
     * These are the different reasons that requires SPF exploration.
     */
    public enum SPFReason {
        OBJECT_CREATION, THROW, EARLYRETURN,
        MULTIPLE, OUT_OF_BOUND_EXCEPTION, INVOKE; //used when the two sides of the ifStmt have SPFCases
    }

    public SPFCaseStmt(Expression spfCondition, SPFReason reason) {
        this.spfCondition = spfCondition;
        this.reason = reason;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "SPFCaseStmt( " + reason + "," + spfCondition.toString() + ")";
    }

    @Override
    public boolean equals(Object stmt2) {
        if (!(stmt2 instanceof SPFCaseStmt))
            return false;
        else {
            String spfCondition2 = ((SPFCaseStmt) stmt2).spfCondition.toString();
            String reason = ((SPFCaseStmt) stmt2).reason.toString();
            return (this.spfCondition.toString().equals(spfCondition2)
                    && this.reason.toString().equals(reason));
        }
    }

    @Override
    public boolean equals(Stmt stmt2) {
        return this.equals((Object)stmt2);
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }
}

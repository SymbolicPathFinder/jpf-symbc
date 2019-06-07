package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * Assignment Statement in RangerIR.
 */
public class AssignmentStmt implements Stmt {

    public final Expression lhs;
    public final Expression rhs;

    public AssignmentStmt(Expression lhs, Expression rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    @Override
    public String toString() {
        return lhs.toString() + " := (" + rhs.toString() +" )";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if (!(stmt2 instanceof AssignmentStmt))
            return false;
        else{
            String lhs2 = ((AssignmentStmt) stmt2).lhs.toString();
            String rhs2 = ((AssignmentStmt) stmt2).rhs.toString();
            return((this.lhs.toString().equals(lhs2)) && (this.rhs.toString().equals(rhs2)));
        }
    }

    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}

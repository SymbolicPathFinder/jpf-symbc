package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

/**
 * RangerIR composition statement.
 */
public class CompositionStmt implements Stmt {
    public final Stmt s1;
    public final Stmt s2;

    public CompositionStmt(Stmt s1, Stmt s2) {
        this.s1 = s1;
        this.s2 = s2;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "(( "+ s1.toString() + ") ; (" + s2.toString() + "))";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if (!(stmt2 instanceof CompositionStmt))
            return false;
        else{
            Stmt s21 = ((CompositionStmt) stmt2).s1;
            Stmt s22 = ((CompositionStmt) stmt2).s2;

            return((this.s1.equals(s21)) && (this.s2.equals(s22)));
        }
    }


}


package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

/**
 * A Skip statement in RangerIR.
 */
public class SkipStmt implements Stmt {

    public static SkipStmt skip = new SkipStmt();

    private SkipStmt() {
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "skip ";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        return (stmt2 instanceof SkipStmt);
    }

}

package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is the IfThenElseStmt in RangerIR that carries a condition instruction and on the "then" and the "else" side the statements extracted from the cfg that represents the two sides of the branch.
 */
public class IfThenElseStmt implements Stmt {
    public final Expression condition;
    public final Stmt thenStmt;
    public final Stmt elseStmt;
    public final SSAConditionalBranchInstruction original;

    public IfThenElseStmt(SSAConditionalBranchInstruction original, Expression condition, Stmt thenStmt, Stmt elseStmt) {
        this.original = original;
        this.condition = condition;
        this.thenStmt = thenStmt;
        this.elseStmt = elseStmt;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return " if (" + this.condition + ") then (" + thenStmt.toString() + ") else (" + elseStmt.toString() + ")";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if (!(stmt2 instanceof IfThenElseStmt))
            return false;
        else {
            String condition2 = ((IfThenElseStmt)stmt2).condition.toString();
            return (this.condition.toString().equals(condition2)
                    && this.thenStmt.equals(((IfThenElseStmt) stmt2).thenStmt)
                    && this.elseStmt.equals(((IfThenElseStmt) stmt2).elseStmt));
        }
    }
}

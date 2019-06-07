package gov.nasa.jpf.symbc.veritesting.ast.visitors;

public class ForallAstVisitor extends AstIterVisitor<Boolean> {

    /**
     * Visits all statements for checking invariants over statements.
     * @param v
     */
    public ForallAstVisitor(ForallExprVisitor v) {
        super(v, (x, y) -> (x && y), Boolean.TRUE);
    }

}

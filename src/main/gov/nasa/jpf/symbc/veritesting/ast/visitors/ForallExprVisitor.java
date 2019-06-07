package gov.nasa.jpf.symbc.veritesting.ast.visitors;

/**
 * A visitor that enforces invariant checking on all expressions by passing the operation and expected result.
 */
public class ForallExprVisitor extends ExprIterVisitor<Boolean> {
    public ForallExprVisitor() {
        super((x, y) -> (x && y), Boolean.TRUE);
    }

}

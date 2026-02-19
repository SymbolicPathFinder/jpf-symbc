package gov.nasa.jpf.symbc.numeric;

public class BitwiseDetector extends ConstraintExpressionVisitor {
    private boolean hasBitwise = false;

    public boolean hasBitwise() {
        return hasBitwise;
    }

    // Visit binary linear integer expressions
    @Override
    public void preVisit(BinaryLinearIntegerExpression expr) {
        checkOperator(expr.getOp());
    }

    // Visit binary non-linear integer expressions (though bitwise ops are linear, we check anyway)
    @Override
    public void preVisit(BinaryNonLinearIntegerExpression expr) {
        checkOperator(expr.op);
    }

    private void checkOperator(Operator op) {
        if (!hasBitwise) {
            switch (op) {
                case AND:
                case OR:
                case XOR:
                case SHIFTL:
                case SHIFTR:
                case SHIFTUR:
                    hasBitwise = true;
                    break;
                default:
                    // nothing
            }
        }
    }

    // The default visit order is:
    //   preVisit(Constraint) -> left.accept(visitor) -> right.accept(visitor) -> postVisit
    // So we are covered.
}
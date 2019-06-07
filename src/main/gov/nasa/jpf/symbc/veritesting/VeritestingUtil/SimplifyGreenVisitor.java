package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.translateNotExpr;


/*
Vaibhav: The functionality currently implemented by this class is made redundant by the SimplifyRangerExprVisitor.
Since we're doing simplification at the Ranger IR level, this class can be removed unless we need a simplification
visitor for Green expressions.
 */
public class SimplifyGreenVisitor extends Visitor {

    public Expression returnExp;

    @Override
    public void postVisit(Operation operation) throws VisitorException {

        Expression e1, e2;

        switch (operation.getOperator()) {
            case AND:
                operation.getOperand(0).accept(this);
                e1 = returnExp;
                operation.getOperand(1).accept(this);
                e2 = returnExp;

                if ((e1 == Operation.FALSE) || (e1 == Operation.FALSE))
                    returnExp = Operation.FALSE;
                else if (e1 == Operation.TRUE)
                    returnExp = e2;
                else if (e2 == Operation.TRUE)
                    returnExp = e1;
                else returnExp = new Operation(Operation.Operator.AND, e1, e2);
                break;

            case OR:
                operation.getOperand(0).accept(this);
                e1 = returnExp;
                operation.getOperand(1).accept(this);
                e2 = returnExp;

                if ((e1 == Operation.TRUE) || (e1 == Operation.TRUE))
                    returnExp = Operation.TRUE;
                else if (e1 == Operation.FALSE)
                    returnExp = e2;
                if (e2 == Operation.FALSE)
                    returnExp = e1;
                else
                    returnExp = new Operation(Operation.Operator.OR, e1, e2);
                break;

            case NOT:
                operation.getOperand(0).accept(this);
                e1 = returnExp;

                if (e1 == Operation.TRUE)
                    returnExp = Operation.FALSE;
                else returnExp = translateNotExpr(operation);
                break;
            default:
                returnExp = operation;
                break;
        }
    }
}

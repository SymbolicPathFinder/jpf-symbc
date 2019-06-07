package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.GreenConstraint;
import gov.nasa.jpf.symbc.numeric.GreenToSPFTranslator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.solvers.SolverTranslator;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.VeritestingListener.performanceMode;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SatResult.DONTKNOW;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SatResult.FALSE;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SatResult.TRUE;

/**
 * A utility class that provides some methods from SPF to Green and vise versa.
 */
public class ExprUtil {

    /**
     * Translates an SPF expression to a Green Expression.
     * @param spfExp SPF Expression
     * @return Green Expression.
     */
    public static Expression SPFToGreenExpr(gov.nasa.jpf.symbc.numeric.Expression spfExp) {
        SolverTranslator.Translator toGreenTranslator = new SolverTranslator.Translator();
        spfExp.accept(toGreenTranslator);
        return toGreenTranslator.getExpression();
    }

    /**
     * Pretty print method to print Green expression.
     * @param expression Green expression.
     * @return String of Green Expression.
     */
    public static String AstToString(Expression expression) {
        if (expression instanceof Operation) {
            Operation operation = (Operation) expression;
            String str = "";
            if (operation.getOperator().getArity() == 2)
                str = "(" + AstToString(operation.getOperand(0)) + " " + operation.getOperator().toString() + " " +
                        AstToString(operation.getOperand(1)) + ")";
            else if (operation.getOperator().getArity() == 1)
                str = "(" + operation.getOperator().toString() + AstToString(operation.getOperand(0)) + ")";
            return str;
        } else
            return expression.toString();
    }

    /**
     * Translates Green Expession to SPF.
     * @param greenExpression A Green expression to be translated to SPF.
     * @return SPF expression.
     */
    public static gov.nasa.jpf.symbc.numeric.Expression greenToSPFExpression(Expression greenExpression) {
        GreenToSPFTranslator toSPFTranslator = new GreenToSPFTranslator();
        gov.nasa.jpf.symbc.numeric.Expression retExp =  toSPFTranslator.translate(greenExpression);
        assert retExp != null;
        return retExp;
    }

    /**
     * Creates a Green variable depending on its type.
     * @param type Type of the variable.
     * @param varId Name of the variable.
     * @return A Green variable.
     */
    public static Expression createGreenVar(String type, String varId) {
        switch (type) {
            case "double":
            case "float":
            case "long":
                return new RealVariable(varId, Double.MIN_VALUE, Double.MAX_VALUE);
            case "int":
            case "short":
            case "boolean":
            default: //considered here an object reference
                return new IntVariable(varId, Integer.MIN_VALUE, Integer.MAX_VALUE);
        }
    }

    public static boolean isConstant(Expression expr) {
        return IntConstant.class.isInstance(expr) || RealConstant.class.isInstance(expr);
    }

    public static boolean isVariable(Expression expr) {
        return WalaVarExpr.class.isInstance(expr) || FieldRefVarExpr.class.isInstance(expr) ||
                ArrayRefVarExpr.class.isInstance(expr) ||
                IntVariable.class.isInstance(expr) || RealVariable.class.isInstance(expr);
    }

    public static String getConstantType(Expression expr) {
        assert isConstant(expr);
        if (IntConstant.class.isInstance(expr)) return "int";
        if (RealConstant.class.isInstance(expr)) return "float";
        return null;
    }

    public static String getGreenVariableType(Expression expr) {
        if (IntVariable.class.isInstance(expr)) return "int";
        if (RealVariable.class.isInstance(expr)) return "float";
        return null;
    }

    /*
    This method tries to avoid a solver call to check satisfiability of the path condition if running in
    performance mode. It avoids the solver call if the isSatisfiable method returns false.
     */
    public static boolean isPCSat(PathCondition pc) throws StaticRegionException {
        long startTime = System.nanoTime();
        boolean isPCSat = isSatisfiable(pc);
        StatisticManager.constPropTime += (System.nanoTime() - startTime);
        // verify that static unsatisfiability is confirmed by solver if we dont want to run fast
        if (!performanceMode && !isPCSat)
            assert (!pc.simplify());
        // in performanceMode, ask the solver for satisfiability only if we didn't find the PC to be unsat.
        if (performanceMode) {
            if (isPCSat) {
                StatisticManager.PCSatSolverCount++;
                startTime = System.nanoTime();
                isPCSat = pc.simplify();
                StatisticManager.PCSatSolverTime += (System.nanoTime() - startTime);
            }
        } else {
            StatisticManager.PCSatSolverCount++;
            startTime = System.nanoTime();
            isPCSat = pc.simplify();
            StatisticManager.PCSatSolverTime += (System.nanoTime() - startTime);
        }
        return isPCSat;
    }

    /*
    TODO: This method needs to be replaced by the use of the SimplifyGreenVisitor. Soha to look into this in the future.
    returns unsatisfiable only if it is certain, else it returns satisfiable. This method doesn't make any solver calls.
    It walks over each expression inside each GreenConstraint and checks if the expression was found to be unsatisfiable.
     */
    public static boolean isSatisfiable(PathCondition pc) throws StaticRegionException {
        Constraint constraint = pc.header;
        while (constraint != null) {
            if (GreenConstraint.class.isInstance(constraint)) {
                Expression greenExpression = ((GreenConstraint) constraint).getExp();
                if (isSatGreenExpression(greenExpression) == FALSE) {
                    System.out.println("found an unsat constraint");
                    return false;
                }
//                try {
//                    greenExpression.accept(satVisitor);
//                } catch (VisitorException e) {
//                    throw new StaticRegionException(e.getMessage());
//                }
            }
            constraint = constraint.and;
        }
        return true;
    }

    public enum SatResult { TRUE, FALSE, DONTKNOW };

    public static SatResult isSatGreenExpression(Expression expression) {
        if (expression instanceof Operation) {
            Operation operation = (Operation) expression;
            SatResult val1 = foldBooleanOp(operation);
            if (val1 != null) return val1;
            if (operation.getArity() == 2) {
                SatResult operand1Sat = isSatGreenExpression(operation.getOperand(0));
                SatResult operand2Sat = isSatGreenExpression(operation.getOperand(1));
                SatResult result;
                switch(operation.getOperator()) {
                    case AND:
                        result = (operand1Sat == FALSE || operand2Sat == FALSE) ? FALSE :
                                ((operand1Sat == TRUE && operand2Sat == TRUE) ? TRUE : DONTKNOW);
                        return result;
                    case OR:
                        result = (operand1Sat == TRUE || operand2Sat == TRUE) ? TRUE:
                            ((operand1Sat == FALSE && operand2Sat == FALSE) ? FALSE: DONTKNOW);
                        return result;
                    default: return DONTKNOW;
                }
            }
            else if (operation.getArity() == 1) {
                SatResult operand1Sat = isSatGreenExpression(operation.getOperand(0));
                if (operand1Sat == DONTKNOW) return DONTKNOW;
                switch(operation.getOperator()) {
                    case NOT: return operand1Sat == FALSE ? TRUE : FALSE;
                    default: return DONTKNOW;
                }
            }
        }
        return DONTKNOW;
    }

    public static SatResult foldBooleanOp(Operation operation) {
        if (operation.getArity() == 2) {
            Expression operand1 = operation.getOperand(0);
            Expression operand2 = operation.getOperand(1);
            if (operand1 instanceof IntConstant && operand2 instanceof IntConstant) {
                int val1 = ((IntConstant)operand1).getValue();
                int val2 = ((IntConstant)operand2).getValue();
                switch(operation.getOperator()) {
                    case EQ: return val1 == val2 ? TRUE: FALSE;
                    case NE: return val1 != val2 ? TRUE: FALSE;
                    case LT: return val1 < val2 ? TRUE: FALSE;
                    case LE: return val1 <= val2 ? TRUE: FALSE;
                    case GT: return val1 > val2 ? TRUE: FALSE;
                    case GE: return val1 >= val2 ? TRUE: FALSE;
                    default: return DONTKNOW;
                }
            }
        } else if (operation.getArity() == 1) {
            Expression operand1 = operation.getOperand(0);
            if (operand1 instanceof IntConstant) {
                int val1 = ((IntConstant) operand1).getValue();
                switch (operation.getOperator()) {
                    case NOT: return val1 == 0 ? TRUE: FALSE;
                    default: return DONTKNOW;
                }
            }
        }
        return null;
    }

    public static Expression translateNotExpr(Operation op) {
        if (op.getOperator() != Operation.Operator.NOT) return op;
        Expression e1 = op.getOperand(0);
        Expression returnExp;
        if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.NOT))
            returnExp = ((Operation) e1).getOperand(0);
        else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.EQ))
            returnExp = new Operation(Operation.Operator.NE, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
        else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.NE))
            returnExp = new Operation(Operation.Operator.EQ, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
        else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.GT))
            returnExp = new Operation(Operation.Operator.LE, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
        else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.GE))
            returnExp = new Operation(Operation.Operator.LT, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
        else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.LE))
            returnExp = new Operation(Operation.Operator.GT, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
        else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.LT))
            returnExp = new Operation(Operation.Operator.GE, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
        else
            returnExp = new Operation(Operation.Operator.NOT, e1);
        return returnExp;
    }

    public static Stmt compose(Stmt s1, Stmt s2, boolean allowBothNull) {
        if (s1 == null && s2 == null) {
            if (!allowBothNull)
                throwException(new IllegalArgumentException("trying to compose with two null statements"),
                    gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.DONTKNOW);
            else return null;
        }
        else if (s1 == null) return s2;
        else if (s2 == null) return s1;
        else return new CompositionStmt(s1, s2);
        return null;
    }

}

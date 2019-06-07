package gov.nasa.jpf.symbc.veritesting.ast.transformations.constprop;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isSatGreenExpression;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.translateNotExpr;
import static java.lang.Math.*;
import static za.ac.sun.cs.green.expr.Operation.FALSE;
import static za.ac.sun.cs.green.expr.Operation.TRUE;

public class SimplifyRangerExprVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    private DynamicTable<Expression> constantsTable;
    public IllegalArgumentException exception = null;
    public boolean somethingChanged = false;

    SimplifyRangerExprVisitor(DynamicTable<Expression> constantsTable) {
        super();
        this.constantsTable = constantsTable;
    }

    private Expression lookup(Expression expr) {
        if (constantsTable.lookup((Variable) expr) != null) {
            somethingChanged = true;
            return constantsTable.lookup((Variable) expr);
        }
        else return expr;
    }


    @Override
    public Expression visit(WalaVarExpr expr) {
        return lookup(expr);
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return lookup(expr);
    }

    @Override
    public Expression visit(IntVariable expr) { return lookup(expr); }

    @Override
    public Expression visit(RealVariable expr) { return lookup(expr); }

    @Override
    public Expression visit(StringVariable expr) { return lookup(expr); }

    @Override
    public Expression visit(AstVarExpr expr) { return lookup(expr); }

    @Override
    public Expression visit(ArrayRefVarExpr expr) { return lookup(expr); }

    @Override
    public Expression visit(Operation expr) {
        Expression ret = null;
        Expression op1 = null, op2 = null;
        //visit operands to populate ret, get op1 and op2 from ret at this point

        if (expr.getArity() == 1) {
            op1 = eva.accept(expr.getOperand(0));
            ret = new Operation(expr.getOperator(), op1);
        }
        if (expr.getArity() == 2) {
            op1 = eva.accept(expr.getOperand(0));
            op2 = eva.accept(expr.getOperand(1));
            ret = new Operation(expr.getOperator(), op1, op2);
        }
        if (ret == null) {
            exception = new IllegalArgumentException("Cannot simplify operator with unknown arity");
            return expr;
        }
        //constant-fold these in when possible by first extracting a method out of ExprUtil.isSatGreenExpression and use the extracted method
        switch (expr.getOperator()) {
            case EQ:
            case NE:
            case LT:
            case LE:
            case GT:
            case GE:
            case AND:
            case OR:
            case NOT:
                ExprUtil.SatResult result;
                result = isSatGreenExpression(ret);
                ret =  result == ExprUtil.SatResult.TRUE ? TRUE:
                        (result == ExprUtil.SatResult.FALSE ? FALSE: translateNotExpr((Operation) ret));
                break;
            case ADD:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() + ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() + ((RealConstant) op2).getValue());
                }
                break;
            case SUB:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() - ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() - ((RealConstant) op2).getValue());
                }
                break;
            case MUL:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() * ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() * ((RealConstant) op2).getValue());
                }
                break;
            case DIV:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() / ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() / ((RealConstant) op2).getValue());
                }
                break;
            case MOD:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() % ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() % ((RealConstant) op2).getValue());
                }
                break;
            case NEG:
                if (op1 instanceof IntConstant) {
                    ret = new IntConstant(-((IntConstant) op1).getValue());
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(-((RealConstant) op1).getValue());
                }
                break;
            case BIT_AND:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() & ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    exception = new IllegalArgumentException("Cannot apply BIT_AND to RealConstant operands");
                }
                break;
            case BIT_OR:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() | ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    exception = new IllegalArgumentException("Cannot apply BIT_OR to RealConstant operands");
                }
                break;
            case BIT_XOR:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() ^ ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    exception = new IllegalArgumentException("Cannot apply BIT_XOR to RealConstant operands");
                }
                break;
            case BIT_NOT:
                if (op1 instanceof IntConstant) {
                    ret = new IntConstant(~((IntConstant) op1).getValue());
                } else if (op1 instanceof RealConstant) {
                    exception = new IllegalArgumentException("Cannot apply BIT_NOT to RealConstant operands");
                }
                break;
            case SHIFTL:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() << ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    exception = new IllegalArgumentException("Cannot apply SHIFTL to RealConstant operands");
                }
                break;
            case SHIFTR:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() >> ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    exception = new IllegalArgumentException("Cannot apply SHIFTR to RealConstant operands");
                }
                break;
            case SHIFTUR:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() >>> ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    exception = new IllegalArgumentException("Cannot apply SHIFTUR to RealConstant operands");
                }
                break;
            case BIT_CONCAT:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
//                    ret = new IntConstant((((IntConstant) op1).getValue() << 32) | ((IntConstant) op2).getValue());
                    exception = new IllegalArgumentException("Dont know how to apply BIT_CONCAT to IntConstant operands");
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    exception = new IllegalArgumentException("Cannot apply BIT_CONCAT to RealConstant operands");
                }
                break;
            case SIN:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply SIN to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(sin(((RealConstant) op1).getValue()));
                }
                break;
            case COS:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply COS to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(cos(((RealConstant) op1).getValue()));
                }
                break;
            case TAN:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply TAN to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(tan(((RealConstant) op1).getValue()));
                }
                break;
            case ASIN:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply ASIN to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(asin(((RealConstant) op1).getValue()));
                }
                break;
            case ACOS:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply ACOS to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(acos(((RealConstant) op1).getValue()));
                }
                break;
            case ATAN:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply ATAN to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(atan(((RealConstant) op1).getValue()));
                }
                break;
            case ATAN2:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply ATAN2 to IntConstant operands");
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(atan2(((RealConstant) op1).getValue(), ((RealConstant) op2).getValue()));
                }
                break;
            case ROUND:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply ROUND to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(round(((RealConstant) op1).getValue()));
                }
                break;
            case LOG:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply LOG to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(log(((RealConstant) op1).getValue()));
                }
                break;
            case EXP:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply EXP to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(exp(((RealConstant) op1).getValue()));
                }
                break;
            case SQRT:
                if (op1 instanceof IntConstant) {
                    exception = new IllegalArgumentException("Cannot apply SQRT to IntConstant operands");
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(sqrt(((RealConstant) op1).getValue()));
                }
                break;
        }
        return ret;
    }

    @Override
    public Expression visit(GammaVarExpr expr) {
        // constant-fold gammas when possible
        Expression cond = eva.accept(expr.condition);
        ExprUtil.SatResult result;
        result = isSatGreenExpression(cond);
        //TODO: throw this gamma away if eva.accept(expr.thenExpr) is equal to eva.accept(expr.elseExpr), instead just
        // return one of those two expressions
        if (result == ExprUtil.SatResult.TRUE) return eva.accept(expr.thenExpr);
        else if (result == ExprUtil.SatResult.FALSE) return eva.accept(expr.elseExpr);
        else {
            Expression thenExpr = eva.accept(expr.thenExpr);
            Expression elseExpr = eva.accept(expr.elseExpr);
            if (thenExpr.equals(elseExpr)) return thenExpr;
            else return new GammaVarExpr(cond, thenExpr, elseExpr);
        }
    }
}

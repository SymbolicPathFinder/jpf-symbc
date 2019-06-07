package gov.nasa.jpf.symbc.numeric;

import java.util.*;

import choco.Problem;
import com.microsoft.z3.*;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

class GreenPbTranslator extends Visitor {

    private ProblemGeneral context = null;

    private Stack<Expr> stack = null;

    private List<Expr> domains = null;

    private Map<Variable, Expr> v2e = null;

    public GreenPbTranslator() {
        this.context = PCParser.pb;
        stack = new Stack<Expr>();
        v2e = new HashMap<Variable, Expr>();
        domains = new LinkedList<Expr>();
    }

    public Object getTranslation() {
        Expr result = stack.pop();
		/* not required due to Bounder being used
		for (BoolExpr expr : domains) {
			try {
				result = context.mkAnd(result,expr);
			} catch (Z3Exception e) {
				e.printStackTrace();
			}
		}
		*/
        return result;
    }

    public Map<Variable, Expr> getVariableMap() {
        return v2e;
    }


    @Override
    public void postVisit(IntConstant constant) {
        try {
            stack.push((Expr) context.makeIntConst(constant.getValue()));
        } catch (Z3Exception e) {
            e.printStackTrace();
        }
    }

    @Override
    public void postVisit(RealConstant constant) {
        try {
            stack.push((Expr) context.makeRealConst(constant.getValue()));
        } catch (Z3Exception e) {
            e.printStackTrace();
        }
    }

    @Override
    public void postVisit(IntVariable variable) {
        Expr v = v2e.get(variable);
        if (v == null) {
            Integer lower = variable.getLowerBound();
            Integer upper = variable.getUpperBound();
            try {
                v = (Expr) context.makeIntVar(variable.getName(),lower,upper);
                // now add bounds
                Expr low  = (Expr) context.geq(v,context.makeIntConst(lower));
                Expr high = (Expr) context.leq(v,context.makeIntConst(upper));
                domains.add((Expr) context.logical_and(low,high));
                PCParser.intVariableMap.put(variable, v);
            } catch (Z3Exception e) {
                e.printStackTrace();
            }
            v2e.put(variable, v);
        }
        stack.push(v);
    }

    @Override
    public void postVisit(RealVariable variable) {
        Expr v = v2e.get(variable);
        if (v == null) {
            int lower = (int) (double) variable.getLowerBound();
            int upper = (int) (double) variable.getUpperBound();
            try {
                v = (Expr) context.makeRealVar(variable.getName(),lower,upper);
                // now add bounds
                Expr low  = (Expr) context.geq(v,context.makeRealConst((double)lower));
                Expr high = (Expr) context.leq(v,context.makeRealConst((double) upper));
                domains.add((Expr) context.logical_and(low,high));
                PCParser.realVariableMap.put(variable, v);
            } catch (Z3Exception e) {
                e.printStackTrace();
            }
            v2e.put(variable, v);
        }
        stack.push(v);
    }

    @Override
    public void postVisit(Operation operation) throws VisitorException {
        Expr l = null;
        Expr r = null;
        int arity = operation.getOperator().getArity();
        if (arity == 2) {
            if (!stack.isEmpty()) {
                r = stack.pop();
            }
            if (!stack.isEmpty()) {
                l = stack.pop();
            }
        } else if (arity == 1) {
            if (!stack.isEmpty()) {
                l = stack.pop();
            }
        }
        try {
            switch (operation.getOperator()) {
                case EQ:
                    stack.push((Expr) context.eq(l, r));
                    break;
                case NE:
                    stack.push((Expr) context.neq(l, r));
                    break;
                case LT:
                    stack.push((Expr) context.lt(l, r));
                    break;
                case LE:
                    stack.push((Expr) context.leq( l, r));
                    break;
                case GT:
                    stack.push((Expr) context.gt( l,  r));
                    break;
                case GE:
                    stack.push((Expr) context.geq( l, r));
                    break;
                case AND:
                    stack.push((Expr) context.logical_and( l, r));
                    break;
                case OR:
                    stack.push((Expr) context.logical_or( l, r));
                    break;
/* Soha: not currently supported in Z3BitVectorProblem in SPF
			case IMPLIES:
				stack.push(context.mkImplies((BoolExpr) l, (BoolExpr) r));
				break;
		*/
                case ADD:
                    stack.push((Expr) context.plus( l, r));
                    break;
                case SUB:
                    stack.push((Expr)context.minus( l, r));
                    break;
                case MUL:
                    stack.push((Expr)context.mult( l, r));
                    break;
                case DIV:
                    stack.push((Expr)context.div( l, r));
                    break;
                case MOD:
                    if (BitVecNum.class.isInstance(r)) {
                        int rValue = ((BitVecNum)r).getInt();
                        // if rValue is a power of 2, we can implement a mod 2^i as a & (2^i–1)
                        if ((rValue & (rValue-1)) == 0) {
                            stack.push((Expr)context.and(l, context.minus(r, 1)));
                        }
                    } else assert(false);
                    break;
                case NEG: assert(false);
                    break;
                case BIT_AND:
                    stack.push((Expr) context.and( l, r));
                    break;
                case BIT_OR:
                    stack.push((Expr) context.or( l, r));
                    break;
                case BIT_XOR:
                    stack.push((Expr) context.xor( l, r));
                    break;
                case BIT_NOT:
                    break;
                case SHIFTL:
                    stack.push((Expr) context.shiftL( l, r));
                    break;
                case SHIFTR:
                    stack.push((Expr) context.shiftR( l, r));
                    break;
                case SHIFTUR:
                    stack.push((Expr) context.shiftUR( l, r));
                    break;
                case NOT:
                    stack.push((Expr) context.logical_not(l));
                    break;
                case IMPLIES:
                case BIT_CONCAT:
                case SIN:
                case COS:
                case TAN:
                case ASIN:
                case ACOS:
                case ATAN:
                case ATAN2:
                case ROUND:
                case LOG:
                case EXP:
                case POWER:
                case SQRT:
                case SUBSTRING:
                case CONCAT:
                case TRIM:
                case REPLACE:
                case REPLACEFIRST:
                case TOLOWERCASE:
                case TOUPPERCASE:
                case VALUEOF:
                case NOTCONTAINS:
                case CONTAINS:
                case LASTINDEXOFCHAR:
                case LASTINDEXOFSTRING:
                case STARTSWITH:
                case NOTSTARTSWITH:
                case ENDSWITH:
                case NOTENDSWITH:
                case EQUALS:
                case NOTEQUALS:
                case EQUALSIGNORECASE:
                case NOTEQUALSIGNORECASE:
                case EMPTY:
                case NOTEMPTY:
                case ISINTEGER:
                case NOTINTEGER:
                case ISFLOAT:
                case NOTFLOAT:
                case ISLONG:
                case NOTLONG:
                case ISDOUBLE:
                case NOTDOUBLE:
                case ISBOOLEAN:
                case NOTBOOLEAN:
                case MATCHES:
                case NOMATCHES:
                case REGIONMATCHES:
                case NOTREGIONMATCHES:
                default:
                    System.out.println("GreenPbTranslator.postVisit does not know how to translate Green operator (" +
                            operation.getOperator() + ") to Z3BitVector" );
                    assert(false);

            }
        } catch (Z3Exception e) {
            e.printStackTrace();
        }
    }
}
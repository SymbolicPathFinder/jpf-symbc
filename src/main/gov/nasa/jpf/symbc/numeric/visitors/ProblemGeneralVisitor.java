package gov.nasa.jpf.symbc.numeric.visitors;

import java.util.HashMap;
import java.util.Map;

import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.BinaryNonLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.BinaryRealExpression;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor2;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
import gov.nasa.jpf.symbc.numeric.MathFunction;
import gov.nasa.jpf.symbc.numeric.MathRealExpression;
import gov.nasa.jpf.symbc.numeric.MixedConstraint;
import gov.nasa.jpf.symbc.numeric.NonLinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.Operator;
import gov.nasa.jpf.symbc.numeric.PCParser;
import gov.nasa.jpf.symbc.numeric.RealConstant;
import gov.nasa.jpf.symbc.numeric.RealConstraint;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemCoral;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVector;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVectorIncremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Incremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Optimize;
import gov.nasa.jpf.symbc.string.StringSymbolic;

public class ProblemGeneralVisitor extends ConstraintExpressionVisitor2 {

	//Idea: Splitting constraints based on LinearIntegerConstraintsVisitor in it's own file. Make the visitor pattern itself more modular.

	//Idea: Change the methods for ProblemGeneral and the solvers to just accept Integer and Long data types. This would solve so many problems
	//and make this class so, so much more simple.

	//Incremental Solver.
	//Static-ness of the class design. (something I'm definitely messing up.)
	//Constraint differences.

	//Regression
	
	//TODO: .accept(this) within the postVisit method. It'll make everything so much nicer.

	//Thought: one main level accept() at the constraint level in postVisit(). It preVisits(this). It postVisits(this)
	//In the postVisit(Constraint constraint) (Or other types of constraints)
	//it then... 
	//accept(left)
	//accept(right) (from within the postVisit method.)
	//Ultimate returns of those are then just used elsewhere.
	//I will need to look at what this accomplishes for the sake of simplicity.

	//postVisit(constraint.getLeft());
	//postVisit(constraint.getRight());

	//TODO:
	//Handling mixed/nonlinerConstraints
	//Correcting names to visit() instead of postVisit() so the readability of accept() statements improves.
	//Stack vs. No Stack - Which do I use and why? Stack feels generally better for many reasons.
	//No stack has prettier accept() methods that make more sense. (These can be cleaned up with a new idea I've had just as I write this)
	//On the other hand, no stack gets rid of many, many ugly instanceof statements.

	static public Map<SymbolicReal, Object>	symRealVar = new HashMap<SymbolicReal,Object>(); // a map between symbolic real variables and DP variables
	static Map<SymbolicInteger,Object>	symIntegerVar = new HashMap<SymbolicInteger,Object>();

	static ProblemGeneral pb;

	/**
	 * CONSTRUCTOR: Creates a ProblemGeneralVisitor object.
	 * Initializes the internal stack and sets the pb object.
	 * @param pb
	 */
	public ProblemGeneralVisitor(ProblemGeneral pb) {
		ProblemGeneralVisitor.pb = pb;
	}

	public void clearVars() {
		symRealVar.clear();
		symIntegerVar.clear();
	}

	public static Map<SymbolicReal, Object> getSymRealVar() {
		return symRealVar;
	}

	public static Map<SymbolicInteger, Object> getSymIntVar() {
		return symIntegerVar;
	}

	//------------------------------------------------------------------------------------------------------------------------------------------
	//RealConstraint methods
	public boolean postVisit(Object left, RealConstraint constraint, Object right) {
		if(left instanceof Double && right instanceof Double) {
			return postVisit(((Double) left), constraint, ((Double) right));
		} else if(left instanceof Double) {
			return postVisit(((Double) left), constraint, right);
		} else if(right instanceof Double) {
			return postVisit(left, constraint, ((Double) right));
		} else {
			switch (constraint.getComparator()) {
			case EQ:
				pb.post(pb.eq(left, right));
				break;
			case NE:
				pb.post(pb.neq(left, right));
				break;
			case LT:
				pb.post(pb.lt(left, right));
				break;
			case LE:
				pb.post(pb.leq(left, right));
				break;
			case GT:
				pb.post(pb.gt(left, right));
				break;
			case GE:
				pb.post(pb.geq(left, right));
				break;
			}
			return true;
		}
	}

	@Override
	public boolean postVisit(Object left, RealConstraint constraint, Double right) {
		Object l = left;
		double r2 = right.doubleValue();
		switch (constraint.getComparator()) {
		case EQ:
			pb.post(pb.eq(l, r2));
			break;
		case NE:
			pb.post(pb.neq(l, r2));
			break;
		case LT:
			pb.post(pb.lt(l, r2));
			break;
		case LE:
			pb.post(pb.leq(l, r2));
			break;
		case GT:
			pb.post(pb.gt(l, r2));
			break;
		case GE:
			pb.post(pb.geq(l, r2));
			break;
		}
		return true;
	}

	@Override
	public boolean postVisit(Double left, RealConstraint constraint, Object right) {
		Object r = right;
		double l2 = left.doubleValue();
		switch (constraint.getComparator()) {
		case EQ:
			pb.post(pb.eq(l2, r));
			break;
		case NE:
			pb.post(pb.neq(l2, r));
			break;
		case LT:
			pb.post(pb.lt(l2, r));
			break;
		case LE:
			pb.post(pb.leq(l2, r));
			break;
		case GT:
			pb.post(pb.gt(l2, r));
			break;
		case GE:
			pb.post(pb.geq(l2, r));
			break;
		}
		return true;
	}

	@Override
	public boolean postVisit(Double left, RealConstraint constraint, Double right) {
		double r2 = right.doubleValue();
		double l2 = left.doubleValue();
		switch (constraint.getComparator()) {
		case EQ:
			if(!(l2 == r2)) {
				return false;
			}
			break;
		case NE:
			if(!(l2 != r2)) {
				return false;
			}
			break;
		case LT:
			if(!(l2 < r2)) {
				return false;
			}
			break;
		case LE:
			if(!(l2 <= r2)) {
				return false;
			}
			break;
		case GT:
			if(!(l2 > r2)) {
				return false;
			}
			break;
		case GE:
			if(!(l2 >= r2)) {
				return false;
			}
			break;
		}
		return true;
	}

	//BRE methods
	@Override
	public Object postVisit(Double lExpr, BinaryRealExpression expression, Double rExpr) {
		throw new RuntimeException("## Error: this is not a symbolic expression");
	}

	@Override
	public Object postVisit(Double lExpr, BinaryRealExpression expression, Object rExpr) {
		Double lExpr2 = lExpr.doubleValue();
		switch (expression.getOp()) {
		case PLUS:
			return pb.plus(lExpr2, rExpr);
		case MINUS:
			return pb.minus(lExpr2, rExpr);
		case MUL:
			return pb.mult(lExpr2, rExpr);
		case DIV:
			return pb.div(lExpr2, rExpr);
		case AND:
			return pb.and(lExpr2, rExpr);
		default:
			System.out.println("Unsupported operation " + expression.getOp());
			throw new RuntimeException();
		}
	}

	@Override
	public Object postVisit(Object lExpr, BinaryRealExpression expression, Double rExpr) {
		Double rExpr2 = rExpr.doubleValue();
		switch (expression.getOp()) {
		case PLUS:
			return pb.plus(lExpr, rExpr2);
		case MINUS:
			return pb.minus(lExpr, rExpr2);
		case MUL:
			return pb.mult(lExpr, rExpr2);
		case DIV:
			return pb.div(lExpr, rExpr2);
		case AND:
			return pb.and(lExpr, rExpr2);
		default:
			System.out.println("Unsupported operation " + expression.getOp());
			throw new RuntimeException();
		}
	}

	@Override
	public Object postVisit(Object lExpr, BinaryRealExpression expression, Object rExpr) {
		if(lExpr instanceof Double && rExpr instanceof Double) {
			return postVisit(((Double) lExpr), expression, ((Double) rExpr));
		} else if(lExpr instanceof Double) {
			return postVisit(((Double) lExpr), expression, rExpr);
		} else if(rExpr instanceof Double) {
			return postVisit(lExpr, expression, ((Double) rExpr));
		} else {
			switch (expression.getOp()) {
			case PLUS:
				return pb.plus(lExpr, rExpr);
			case MINUS:
				return pb.minus(lExpr, rExpr);
			case MUL:
				return pb.mult(lExpr, rExpr);
			case DIV:
				return pb.div(lExpr, rExpr);
			case AND:
				return pb.and(lExpr, rExpr);
			default:
				System.out.println("Unsupported operation " + expression.getOp());
				throw new RuntimeException();
			}
		}
	}

	//Constant method
	@Override
	public Double postVisit(RealConstant realConstant) {
		Double value = realConstant.value;
		return value;
	}

	//SymReal method
	@Override
	public Object postVisit(SymbolicReal symbReal) {
		assert(symbReal._min>=Double.MIN_VALUE && symbReal._max<=Double.MAX_VALUE);
		Object dp_var = symRealVar.get(symbReal);

		if (dp_var == null) {
			dp_var = pb.makeRealVar(symbReal.getName(), symbReal._min, symbReal._max);
			symRealVar.put(symbReal, dp_var);
		}
		return dp_var;
	}

	//MathRealExpression method - Needs further testing since I use null values for rightExpr a lot.
	@Override
	public Object postVisit(Object leftExpr, MathRealExpression mathRealExpr, Object rightExpr) {
		switch(mathRealExpr.op){
		case SIN:
			assert rightExpr == null;
			return pb.sin(leftExpr);
		case COS:
			assert rightExpr == null;
			return pb.cos(leftExpr);
		case EXP:
			assert rightExpr == null;
			return pb.exp(leftExpr);
		case ASIN:
			assert rightExpr == null;
			return pb.asin(leftExpr);
		case ACOS:
			assert rightExpr == null;
			return pb.acos(leftExpr);
		case ATAN:
			assert rightExpr == null;
			return pb.atan(leftExpr);
		case LOG:
			assert rightExpr == null;
			return pb.log(leftExpr);
		case TAN:
			assert rightExpr == null;
			return pb.tan(leftExpr);
		case SQRT:
			assert rightExpr == null;
			return pb.sqrt(leftExpr);
		case POW:
			if(leftExpr instanceof Double) {
				return pb.power(((Double)leftExpr).doubleValue(), rightExpr);
			} else if(rightExpr instanceof Double) {
				return pb.power(leftExpr, ((Double)rightExpr).doubleValue());
			} else {
				return pb.power(leftExpr, rightExpr);
			}
		case ATAN2:
			if(leftExpr instanceof Double) {
				return pb.atan2(((Double)leftExpr).doubleValue(), rightExpr);
			} else if(rightExpr instanceof Double) {
				return pb.atan2(leftExpr, ((Double)rightExpr).doubleValue());
			} else {
				return pb.atan2(leftExpr, rightExpr);
			}
		default:
			throw new RuntimeException("## Error: Expression " + mathRealExpr);
		}
	}

	//------------------------------------------------------------------------------------------------------------------------------------------
	//LinearIntegerConstraint Methods
	@Override
	public boolean postVisit(Long left, LinearIntegerConstraint constraint, Long right) {
		long r2 = right.longValue();
		long l2 = left.longValue();
		switch (constraint.getComparator()) {
		case EQ:
			if(!(l2 == r2)) {
				return false;
			}
			break;
		case NE:
			if(!(l2 != r2)) {
				return false;
			}
			break;
		case LT:
			if(!(l2 < r2)) {
				return false;
			}
			break;
		case LE:
			if(!(l2 <= r2)) {
				return false;
			}
			break;
		case GT:
			if(!(l2 > r2)) {
				return false;
			}
			break;
		case GE:
			if(!(l2 >= r2)) {
				return false;
			}
			break;
		}
		return true;
	}

	@Override
	public boolean postVisit(Long left, LinearIntegerConstraint constraint, Object right) {
		long left2 = left.longValue();
		switch (constraint.getComparator()) {
		case EQ:
			pb.post(pb.eq(left2, right));
			break;
		case NE:
			pb.post(pb.neq(left2, right));
			break;
		case LT:
			pb.post(pb.lt(left2, right));
			break;
		case LE:
			pb.post(pb.leq(left2, right));
			break;
		case GT:
			pb.post(pb.gt(left2, right));
			break;
		case GE:
			pb.post(pb.geq(left2, right));
			break;
		}
		return true;
	}

	@Override
	public boolean postVisit(Object left, LinearIntegerConstraint constraint, Long right) {
		long right2 = right.longValue();
		switch (constraint.getComparator()) {
		case EQ:
			pb.post(pb.eq(left, right2));
			break;
		case NE:
			pb.post(pb.neq(left, right2));
			break;
		case LT:
			pb.post(pb.lt(left, right2));
			break;
		case LE:
			pb.post(pb.leq(left, right2));
			break;
		case GT:
			pb.post(pb.gt(left, right2));
			break;
		case GE:
			pb.post(pb.geq(left, right2));
			break;
		}
		return true;
	}

	@Override
	public boolean postVisit(Object left, LinearIntegerConstraint constraint, Object right) {
		if(left instanceof Long && right instanceof Long) {
			return postVisit(((Long) left), constraint, ((Long) right));
		} else if(left instanceof Long) {
			return postVisit(((Long) left), constraint, right);
		} else if(right instanceof Long) {
			return postVisit(left, constraint, ((Long) right));
		} else {
			switch (constraint.getComparator()) {
			case EQ:
				pb.post(pb.eq(left, right));
				break;
			case NE:
				pb.post(pb.neq(left, right));
				break;
			case LT:
				pb.post(pb.lt(left, right));
				break;
			case LE:
				pb.post(pb.leq(left, right));
				break;
			case GT:
				pb.post(pb.gt(left, right));
				break;
			case GE:
				pb.post(pb.geq(left, right));
				break;
			}
			return true;
		}
	}

	//NonLinearIntegerConstraint Methods
	@Override
	public boolean postVisit(Long left, NonLinearIntegerConstraint constraint, Long right) {
		long r2 = right.longValue();
		long l2 = left.longValue();
		switch (constraint.getComparator()) {
		case EQ:
			if(!(l2 == r2)) {
				return false;
			}
			break;
		case NE:
			if(!(l2 != r2)) {
				return false;
			}
			break;
		case LT:
			if(!(l2 < r2)) {
				return false;
			}
			break;
		case LE:
			if(!(l2 <= r2)) {
				return false;
			}
			break;
		case GT:
			if(!(l2 > r2)) {
				return false;
			}
			break;
		case GE:
			if(!(l2 >= r2)) {
				return false;
			}
			break;
		}
		return true;
	}
	
	@Override
	public boolean postVisit(Long left, NonLinearIntegerConstraint constraint, Object right) {
		long left2 = left.longValue();
		switch (constraint.getComparator()) {
		case EQ:
			pb.post(pb.eq(left2, right));
			break;
		case NE:
			pb.post(pb.neq(left2, right));
			break;
		case LT:
			pb.post(pb.lt(left2, right));
			break;
		case LE:
			pb.post(pb.leq(left2, right));
			break;
		case GT:
			pb.post(pb.gt(left2, right));
			break;
		case GE:
			pb.post(pb.geq(left2, right));
			break;
		}
		return true;
	}
	
	@Override
	public boolean postVisit(Object left, NonLinearIntegerConstraint constraint, Long right) {
		long right2 = right.longValue();
		switch (constraint.getComparator()) {
		case EQ:
			pb.post(pb.eq(left, right2));
			break;
		case NE:
			pb.post(pb.neq(left, right2));
			break;
		case LT:
			pb.post(pb.lt(left, right2));
			break;
		case LE:
			pb.post(pb.leq(left, right2));
			break;
		case GT:
			pb.post(pb.gt(left, right2));
			break;
		case GE:
			pb.post(pb.geq(left, right2));
			break;
		}
		return true;
	}
	
	@Override
	public boolean postVisit(Object left, NonLinearIntegerConstraint constraint, Object right) {
		if(pb instanceof ProblemCoral || pb instanceof ProblemZ3|| pb instanceof ProblemZ3Optimize || 
				pb instanceof ProblemZ3BitVector || pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {
			if(left instanceof Long && right instanceof Long) {
				return postVisit(((Long) left), constraint, ((Long) right));
			} else if(left instanceof Long) {
				return postVisit(((Long) left), constraint, right);
			} else if(right instanceof Long) {
				return postVisit(left, constraint, ((Long) right));
			} else {
				switch (constraint.getComparator()) {
				case EQ:
					pb.post(pb.eq(left, right));
					break;
				case NE:
					pb.post(pb.neq(left, right));
					break;
				case LT:
					pb.post(pb.lt(left, right));
					break;
				case LE:
					pb.post(pb.leq(left, right));
					break;
				case GT:
					pb.post(pb.gt(left, right));
					break;
				case GE:
					pb.post(pb.geq(left, right));
					break;
				}
				return true;
			}
		} else {
			throw new RuntimeException("## Error: Non Linear Integer Constraint not handled " + constraint);
		}
	}
	
	//Methods for BLIES
	@Override
	public Object postVisit(Long lExpr, BinaryLinearIntegerExpression expression, Long rExpr) {
		throw new RuntimeException("## Error: this is not a symbolic expression");
	}

	@Override
	public Object postVisit(Object lExpr, BinaryLinearIntegerExpression expression, Long rExpr) {
		long rExpr2 = rExpr.longValue();
		switch (expression.getOp()) {
		case PLUS:
			return pb.plus(lExpr, rExpr2);
		case MINUS:
			return pb.minus(lExpr, rExpr2);
		case MUL:
			return pb.mult(lExpr, rExpr2);
		case DIV:
			return pb.div(lExpr, rExpr2);
		case REM:
			return pb.rem(lExpr, rExpr2);
		case AND:
			return pb.and(lExpr, rExpr2);
		case OR:
			return pb.or(lExpr, rExpr2);
		case XOR:
			return pb.xor(lExpr, rExpr2);
		case SHIFTR:
			return pb.shiftR(lExpr, rExpr2);
		case SHIFTUR:
			return pb.shiftUR(lExpr, rExpr2);
		case SHIFTL:
			return pb.shiftL(lExpr, rExpr2);
		default:
			System.out.println("Error : unsupported operation " + expression.getOp());
			throw new RuntimeException();
		}
	}

	@Override
	public Object postVisit(Long lExpr, BinaryLinearIntegerExpression expression, Object rExpr) {
		long lExpr2 = lExpr.longValue();
		switch (expression.getOp()) {
		case PLUS:
			return pb.plus(lExpr2, rExpr);
		case MINUS:
			return pb.minus(lExpr2, rExpr);
		case MUL:
			return pb.mult(lExpr2, rExpr);
		case DIV:
			return pb.div(lExpr2, rExpr);
		case REM:
			return pb.rem(lExpr2, rExpr);
		case AND:
			return pb.and(lExpr2, rExpr);
		case OR:
			return pb.or(lExpr2, rExpr);
		case XOR:
			return pb.xor(lExpr2, rExpr);
		case SHIFTR:
			return pb.shiftR(lExpr2, rExpr);
		case SHIFTUR:
			return pb.shiftUR(lExpr2, rExpr);
		case SHIFTL:
			return pb.shiftL(lExpr2, rExpr);
		default:
			System.out.println("Error : unsupported operation " + expression.getOp());
			throw new RuntimeException();
		}
	}

	@Override
	public Object postVisit(Object lExpr, BinaryLinearIntegerExpression expression, Object rExpr) {
		if(lExpr instanceof Long && rExpr instanceof Long) {
			return postVisit(((Long) lExpr), expression, ((Long) rExpr));
		} else if(lExpr instanceof Long) {
			return postVisit(((Long) lExpr), expression, rExpr);
		} else if(rExpr instanceof Long) {
			return postVisit(lExpr, expression, ((Long) rExpr));
		} else {
			switch (expression.getOp()) {
			case PLUS:
				return pb.plus(lExpr, rExpr);
			case MINUS:
				return pb.minus(lExpr, rExpr);
			case MUL:
				throw new RuntimeException("## Error: Binary Non Linear Operation");
			case DIV:
				throw new RuntimeException("## Error: Binary Non Linear Operation");
			case REM:
				throw new RuntimeException("## Error: Binary Non Linear Operation");
			case AND:
				return pb.and(lExpr, rExpr);
			case OR:
				return pb.or(lExpr, rExpr);
			case XOR:
				return pb.xor(lExpr, rExpr);
			case SHIFTR:
				return pb.shiftR(lExpr, rExpr);
			case SHIFTUR:
				return pb.shiftUR(lExpr, rExpr);
			case SHIFTL:
				return pb.shiftL(lExpr, rExpr);
			default:
				throw new RuntimeException("Error : unsupported operation " + expression.getOp());
			}
		}
	}

	//Methods for BNLIES
	@Override
	public Object postVisit(Long lExpr, BinaryNonLinearIntegerExpression expression, Long rExpr) {
		throw new RuntimeException("## Error: this is not a symbolic expression");
	}

	@Override
	public Object postVisit(Object lExpr, BinaryNonLinearIntegerExpression expression, Long rExpr) {
		long rExpr2 = rExpr.longValue();
		switch (expression.op) {
		case PLUS:
			return pb.plus(lExpr, rExpr2);
		case MINUS:
			return pb.minus(lExpr, rExpr2);
		case MUL:
			return pb.mult(lExpr, rExpr2);
		case DIV:
			return pb.div(lExpr, rExpr2);
		case REM:
			return pb.rem(lExpr, rExpr2);
		case AND:
			return pb.and(lExpr, rExpr2);
		case OR:
			return pb.or(lExpr, rExpr2);
		case XOR:
			return pb.xor(lExpr, rExpr2);
		case SHIFTR:
			return pb.shiftR(lExpr, rExpr2);
		case SHIFTUR:
			return pb.shiftUR(lExpr, rExpr2);
		case SHIFTL:
			return pb.shiftL(lExpr, rExpr2);
		default:
			throw new RuntimeException("Error : unsupported operation " + expression.op);
		}
	}

	@Override
	public Object postVisit(Long lExpr, BinaryNonLinearIntegerExpression expression, Object rExpr) {
		long lExpr2 = lExpr.longValue();
		switch (expression.op) {
		case PLUS:
			return pb.plus(lExpr2, rExpr);
		case MINUS:
			return pb.minus(lExpr2, rExpr);
		case MUL:
			return pb.mult(lExpr2, rExpr);
		case DIV:
			return pb.div(lExpr2, rExpr);
		case REM:
			return pb.rem(lExpr2, rExpr);
		case AND:
			return pb.and(lExpr2, rExpr);
		case OR:
			return pb.or(lExpr2, rExpr);
		case XOR:
			return pb.xor(lExpr2, rExpr);
		case SHIFTR:
			return pb.shiftR(lExpr2, rExpr);
		case SHIFTUR:
			return pb.shiftUR(lExpr2, rExpr);
		case SHIFTL:
			return pb.shiftL(lExpr2, rExpr);
		default:
			throw new RuntimeException("Error : unsupported operation " + expression.op);
		}
	}

	@Override
	public Object postVisit(Object lExpr, BinaryNonLinearIntegerExpression expression, Object rExpr) {
		//TODO: Get rid of this terrible instanceof statement for solver types.
		//Make a true/false for BNLIE supported pb's and just check that.
		if(pb instanceof ProblemCoral || pb instanceof ProblemZ3 || pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3BitVector ||
				pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {
			if(lExpr instanceof Long && rExpr instanceof Long) {
				return postVisit(((Long) lExpr), expression, ((Long) rExpr));
			} else if(lExpr instanceof Long) {
				return postVisit(((Long) lExpr), expression, rExpr);
			} else if(rExpr instanceof Long) {
				return postVisit(lExpr, expression, ((Long) rExpr));
			} else {
				switch (expression.op) {
				case PLUS:
					return pb.plus(lExpr, rExpr);
				case MINUS:
					return pb.minus(lExpr, rExpr);
				case MUL:
					return pb.mult(lExpr, rExpr);
				case DIV:
					return pb.div(lExpr, rExpr);
				case REM:
					return pb.rem(lExpr, rExpr);
				case AND:
					return pb.and(lExpr, rExpr);
				case OR:
					return pb.or(lExpr, rExpr);
				case XOR:
					return pb.xor(lExpr, rExpr);
				case SHIFTR:
					return pb.shiftR(lExpr, rExpr);
				case SHIFTUR:
					return pb.shiftUR(lExpr, rExpr);
				case SHIFTL:
					return pb.shiftL(lExpr, rExpr);
				default:
					throw new RuntimeException("Error : unsupported operation " + expression.op);
				}
			}
		} else {
			//It's not a solver that can solveBinaryNonLinearIntegerExpressions.
			throw new RuntimeException("Selected solver type cannot solve BinaryNonLinearIntegerExpressions");
		}
	}

	//Integer Method
	@Override
	public Long postVisit(IntegerConstant integerConstant) {
		Long value = integerConstant.value;
		return value;
	}

	//SymbInt Method
	@Override
	public Object postVisit(SymbolicInteger symbInt) {
		assert(symbInt._min >= Integer.MIN_VALUE && symbInt._max <= Integer.MAX_VALUE);
		Object dp_var = symIntegerVar.get(symbInt);

		if (dp_var == null) {
			dp_var = pb.makeIntVar(((SymbolicInteger)symbInt).getName(),((SymbolicInteger)symbInt)._min, ((SymbolicInteger)symbInt)._max);
			symIntegerVar.put((SymbolicInteger)symbInt, dp_var);
		}
		return dp_var;
	}

	//------------------------------------------------------------------------------------------------------------------------------------------
	//MixedConstraint stuff.
	@Override
	public boolean postVisit(RealExpression left, MixedConstraint constraint, IntegerExpression right) {
		assert(false); // should not be reachable. I kept the functionality as it was in PCParser, but I feel like throwing a RuntimeException is probably better.
		return true; 
	}
	
	@Override
	public boolean postVisit(RealExpression left, MixedConstraint constraint, SymbolicInteger right) {
		assert (constraint.getComparator() == Comparator.EQ);

		Object l = left.accept(this);
		Object r = right.accept(this);
		
		Object tmpr = pb.makeRealVar(left + "_" + left.hashCode(), ((SymbolicInteger)right)._min, ((SymbolicInteger)right)._max);
		if(left instanceof RealConstant) {
			pb.post(pb.eq(tmpr, ((RealConstant)left).value));
		} else {
			pb.post(pb.eq(tmpr, l));
		}
		pb.post(pb.mixed(tmpr, r));
		return true;
	}

	@Override
	public boolean postVisit(SymbolicReal left, MixedConstraint constraint, IntegerExpression right) {
		assert (constraint.getComparator() == Comparator.EQ);

		Object l = left.accept(this);

		Object tmpi = pb.makeIntVar(right + "_" + right.hashCode(),(int)(((SymbolicReal)left)._min), (int)(((SymbolicReal)left)._max));

		if (right instanceof IntegerConstant) { //If the right value is a constant.
			pb.post(pb.eq(((IntegerConstant)right).value,tmpi));
		} else {
			Object r = right.accept(this);
			pb.post(pb.eq(r,tmpi));
		}
		pb.post(pb.mixed(l,tmpi));
		return true;
	}
	
	@Override
	public boolean postVisit(SymbolicReal left, MixedConstraint constraint, SymbolicInteger right) {
		assert (constraint.getComparator() == Comparator.EQ);

		Object l = left.accept(this);
		Object r = right.accept(this);

		pb.post(pb.mixed(l, r));
		
		return true;
	}

	
	//TODO: Stuff from here.
	@Override 
	public void postVisit(LogicalORLinearIntegerConstraints constraint) {
		//TODO: I'll get to this. This appears to be there to handle CNF style constraints, whatever those are.
	}

}
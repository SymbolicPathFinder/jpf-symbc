package gov.nasa.jpf.symbc.numeric.visitors;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.BinaryRealExpression;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.MathFunction;
import gov.nasa.jpf.symbc.numeric.MathRealExpression;
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

public class ProblemGeneralVisitor extends ConstraintExpressionVisitor {

	/**
	 * 
	 */
	static public Map<SymbolicReal, Object>	symRealVar = new HashMap<SymbolicReal,Object>(); // a map between symbolic real variables and DP variables
	static Map<SymbolicInteger,Object>	symIntegerVar = new HashMap<SymbolicInteger,Object>();
	/**
	 * 
	 */
	private Stack<Object> stack;

	/**
	 * 
	 */
	private ProblemGeneral pb;
	
	/**
	 * CONSTRUCTOR: Creates a ProblemGeneralVisitor object.
	 * Initializes the internal stack and sets the pb object.
	 * @param pb
	 */
	public ProblemGeneralVisitor(ProblemGeneral pb) {
		stack = new Stack<Object>();
		this.pb = pb;
	}

//	These next 5 methods, postVisits for RealConstraint, BinaryRealExpression, RealConstant, SymbolicReal, and MathRealExpression
//	Work by taking into consideration the work that is originally being done in PCParser.java's createDPRealConstraint(RealConstraint)
//	Method for constraints. Some functionality may be mirrored from future work that I do on this.
	
	@Override
	public void postVisit(RealConstraint constraint) {
		
		//TODO: Out of the functionality this is supposed to imitate within PCParser, the check and return for true/false
		//under the condition where l and r are both RealConstants is missing.
		Object l;
		Object r;
		switch (constraint.getComparator()) {
			case EQ:
				r = stack.pop();
				l = stack.pop();
				pb.post(pb.eq(l, r));
				break;
			case NE:
				r = stack.pop();
				l = stack.pop();
				pb.post(pb.neq(l, r));
				break;
			case LT:
				r = stack.pop();
				l = stack.pop();
				pb.post(pb.lt(l, r));
				break;
			case LE:
				r = stack.pop();
				l = stack.pop();
				pb.post(pb.leq(l, r));
				break;
			case GT:
				r = stack.pop();
				l = stack.pop();
				pb.post(pb.gt(l, r));
				break;
			case GE:
				r = stack.pop();
				l = stack.pop();
				pb.post(pb.geq(l, r));
				break;
		}
	}

	/**
	 * This does the heavy lifting for BinaryRealExpression.
	 */
	@Override
	public void postVisit(BinaryRealExpression expression) {
		
		//TODO: throw new RuntimeException("## Error: this is not a symbolic expression");
		//I'm missing the places where these sorts of errors are thrown, and I'm not sure how to go about handling these.
		Object l;
		Object r;
		switch (expression.getOp()) {
			case PLUS:
				r = stack.pop();
				l = stack.pop();
				stack.push(pb.plus(l, r));
				break;
			case MINUS:
				r = stack.pop();
				l = stack.pop();
				stack.push(pb.minus(l, r));
				break;
			case MUL:
				r = stack.pop();
				l = stack.pop();
				stack.push(pb.mult(l, r));
				break;
			default:
				System.out.println("ProblemGeneralTranslator : unsupported operation " + expression.getOp());
				//Let's add the rest later. This should work for now.
				throw new RuntimeException();
		}
	}

	/**
	 * This is adding the double value to the stack
	 */
	@Override
	public void postVisit(RealConstant realConstant) {
		//Let's roll with this for now. Just adding the value to the stack.
		stack.add(realConstant.value);
	}

	/**
	 * This is adding the dp_var for the SymbolicReal to the stack.
	 */
	@Override
	public void postVisit(SymbolicReal symbReal) {
		assert(symbReal._min>=Double.MIN_VALUE && symbReal._max<=Double.MAX_VALUE);
		Object dp_var = symRealVar.get(symbReal);
		
		if (dp_var == null) {
			dp_var = pb.makeRealVar(symbReal.getName(), symbReal._min, symbReal._max);
			symRealVar.put(symbReal, dp_var);
		}
		
		stack.add(dp_var);
	}
	
	/**
	 * This is adding the result of various mathExpressions to the stack.
	 */
	@Override
	public void postVisit(MathRealExpression mathRealExpr) {

		Object	l;
		Object	r;
		switch(mathRealExpr.op){
			case SIN:
				l = stack.pop();
				stack.push(pb.sin(l));
				break;
			case COS:
				l = stack.pop();
				stack.push(pb.cos(l));
				break;
			case EXP:
				l = stack.pop();
				stack.push(pb.exp(l));
				break;
			case ASIN:
				l = stack.pop();
				stack.push(pb.asin(l));
				break;
			case ACOS:
				l = stack.pop();
				stack.push(pb.acos(l));
				break;
			case ATAN:
				l = stack.pop();
				stack.push(pb.atan(l));
				break;
			case LOG:
				l = stack.pop();
				stack.push(pb.log(l));
				break;
			case TAN:
				l = stack.pop();
				stack.push(pb.tan(l));
				break;
			case SQRT:
				l = stack.pop();
				stack.push(pb.sqrt(l));
				break;
			case POW:
				r = stack.pop();
				l = stack.pop();
				stack.push(pb.power(l, r));
				break;
			case ATAN2:
				r = stack.pop();
				l = stack.pop();
				stack.push(pb.atan2(l, r));
				break;
			default:
				throw new RuntimeException("## Error: Expression " + mathRealExpr);
		}
	}
	
	@Override
	public void postVisit(LinearIntegerConstraint Constraint) {
		//Does something even need to happen here?
	}
	
	@Override
	public void postVisit(BinaryLinearIntegerExpression expression) {
		
		//TODO: WIP
		if(pb instanceof ProblemCoral || pb instanceof ProblemZ3 || pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3BitVector ||
		          pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {
			
		}
	}
	
	@Override
	public void postVisit(IntegerConstant integerConstant) {
		//Let's roll with this for now. Just adding the value to the stack.
		stack.add(integerConstant.value);
	}
	
	@Override
	public void postVisit(SymbolicInteger symbInt) {
		assert(symbInt._min >= Integer.MIN_VALUE && symbInt._max <= Integer.MAX_VALUE);
		Object dp_var = symIntegerVar.get(symbInt);
		
		if (dp_var == null) {
			dp_var = pb.makeIntVar(symbInt.getName(), symbInt._min, symbInt._max);
			symIntegerVar.put(symbInt, dp_var);
		}
		
		stack.add(dp_var);
	}
	
	

	
	
//	@Override
//	public void preVisit(LinearIntegerConstraint lIConstraint) {
//		PCParser.createDPLinearIntegerConstraint(lIConstraint);
//	}
	
	
//	@Override
//	public void postVisit(SymbolicReal realVariable) {
//		variables.add(realVariable);
//	}
//
//	@Override
//	public void postVisit(SymbolicInteger integerVariable) {
//		variables.add(integerVariable);
//	}
//	
//	@Override
//	public void postVisit(StringSymbolic stringVariable) {
//		variables.add(stringVariable);
//	}
//
//	public Set<Expression> getVariables() {
//		return variables;
//	}

}
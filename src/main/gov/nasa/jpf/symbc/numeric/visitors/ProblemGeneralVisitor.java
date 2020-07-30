package gov.nasa.jpf.symbc.numeric.visitors;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.BinaryNonLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.BinaryRealExpression;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
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

public class ProblemGeneralVisitor extends ConstraintExpressionVisitor {

	//Incremental Solver.
	//Static-ness of the class design. (something I'm definitely messing up.)
	//Constraint differences.
	
	//Difference between BLIE and BNLIE and whether BLIE can handle those types of expressions if the solver can.
	//Handling mixed/nonlinerConstraints/arrays all get complicated and I want to determine details.
	//If I reformat these to just return Objects, I can technically avoid using a stack altogether, right?
	//Handling the returning true/false values of the constraints themselves. Maybe something like a return after successfully posting something so I can just use the way 
	//PC parser uses to iterate through all the constraints.
	
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
	static ProblemGeneral pb;
	
	/**
	 * CONSTRUCTOR: Creates a ProblemGeneralVisitor object.
	 * Initializes the internal stack and sets the pb object.
	 * @param pb
	 */
	public ProblemGeneralVisitor(ProblemGeneral pb) {
		stack = new Stack<Object>();
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
	
	//	These next 5 methods, postVisits for RealConstraint, BinaryRealExpression, RealConstant, SymbolicReal, and MathRealExpression
	//	Work by taking into consideration the work that is originally being done in PCParser.java's createDPRealConstraint(RealConstraint)
	//	Method for constraints. Some functionality may be mirrored from future work that I do on this.
	
	
	//Idea: Make a true/false for BNLIE supported pb's and just check that.

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

		Object l;
		Object r;
		switch (expression.getOp()) {
		case PLUS:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Double && r instanceof Double) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.plus(l, r));
			}
			break;
		case MINUS:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Double && r instanceof Double) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.minus(l, r));
			}
			break;
		case MUL:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Double && r instanceof Double) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.mult(l, r));
			}
			break;
		case DIV:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Double && r instanceof Double) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.div(l, r));
			}
			break;
		case AND:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Double && r instanceof Double) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.and(l, r));
			}
			break;
		default:
			System.out.println("ProblemGeneralTranslator : unsupported operation " + expression.getOp());
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
	public void postVisit(Constraint constraint) {
		//A general case method for constraints may just be the correct way to go about this after all.
		
		//Problem = having these two as Objects prevents me from accessing Long or Double values as I need them,
		//since the methods use primitive data type versions and I'm telling these to make objects, so they're
		//falling under the wrong method. I could use a bunch of instanceof if statements here to accomplish it.
		//I suppose I could also have a check for IntegerContant/RealConstant values and change them to what I want.
		//Additionally, I could make more methods to overload and differentiate between return values and the like
		//It would circumvent the need for a stack, but dramatically increase the number of methods I'd need to 
		//write.
		
		//So overall I have 3 different solution options here, but I'm not sure which direction I would want to go in.
		
		//Once I solve the above issue, I'm fairly confident I'll have it working.
		
		//postVisit(IntegerConstant ic, comparator c, Object r) methods like this would probably solve this.
		Object r = stack.pop();
		Object l = stack.pop();
		
		switch (constraint.getComparator()) {
		case EQ:
			if(r instanceof IntegerConstant && l instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				int l2 = ((IntegerConstant) l).value();
				//pb.post(pb.eq(l2, r2));
				//This just needs a check for equality. I do not like this solution. I need to think about how
				//To make this not terrible.
			} else if(l instanceof IntegerConstant) {
				int l2 = ((IntegerConstant) l).value();
				pb.post(pb.eq(l2, r));
			} else if(r instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				pb.post(pb.eq(l, r2));
			} else {
				pb.post(pb.eq(l, r));
			}
			break;
		case NE:
			if(r instanceof IntegerConstant && l instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				int l2 = ((IntegerConstant) l).value();
				//pb.post(pb.eq(l2, r2));
				//This just needs a check for equality. I do not like this solution. I need to think about how
				//To make this not terrible.
			} else if(l instanceof IntegerConstant) {
				int l2 = ((IntegerConstant) l).value();
				pb.post(pb.neq(l2, r));
			} else if(r instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				pb.post(pb.neq(l, r2));
			} else {
				pb.post(pb.neq(l, r));
			}
			break;
		case LT:
			if(r instanceof IntegerConstant && l instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				int l2 = ((IntegerConstant) l).value();
				//pb.post(pb.eq(l2, r2));
				//This just needs a check for equality. I do not like this solution. I need to think about how
				//To make this not terrible.
			} else if(l instanceof IntegerConstant) {
				int l2 = ((IntegerConstant) l).value();
				pb.post(pb.lt(l2, r));
			} else if(r instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				pb.post(pb.lt(l, r2));
			} else {
				pb.post(pb.lt(l, r));
			}
			break;
		case LE:
			if(r instanceof IntegerConstant && l instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				int l2 = ((IntegerConstant) l).value();
				//pb.post(pb.eq(l2, r2));
				//This just needs a check for equality. I do not like this solution. I need to think about how
				//To make this not terrible.
			} else if(l instanceof IntegerConstant) {
				int l2 = ((IntegerConstant) l).value();
				pb.post(pb.leq(l2, r));
			} else if(r instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				pb.post(pb.leq(l, r2));
			} else {
				pb.post(pb.leq(l, r));
			}
			break;
		case GT:
			if(r instanceof IntegerConstant && l instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				int l2 = ((IntegerConstant) l).value();
				//pb.post(pb.eq(l2, r2));
				//This just needs a check for equality. I do not like this solution. I need to think about how
				//To make this not terrible.
			} else if(l instanceof IntegerConstant) {
				int l2 = ((IntegerConstant) l).value();
				pb.post(pb.gt(l2, r));
			} else if(r instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				pb.post(pb.gt(l, r2));
			} else {
				pb.post(pb.gt(l, r));
			}
			break;
		case GE:
			if(r instanceof IntegerConstant && l instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				int l2 = ((IntegerConstant) l).value();
				//pb.post(pb.eq(l2, r2));
				//This just needs a check for equality. I do not like this solution. I need to think about how
				//To make this not terrible.
			} else if(l instanceof IntegerConstant) {
				int l2 = ((IntegerConstant) l).value();
				pb.post(pb.geq(l2, r));
			} else if(r instanceof IntegerConstant) {
				int r2 = ((IntegerConstant) r).value();
				pb.post(pb.geq(l, r2));
			} else {
				pb.post(pb.geq(l, r));
			}
			break;
		}
		
	}

	
	
	@Override
	public void postVisit(BinaryNonLinearIntegerExpression expression) {
		//For BNLIEs we need to make sure that the proper type of solver is being used to handle them.
		if(pb instanceof ProblemCoral || pb instanceof ProblemZ3 || pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3BitVector ||
		          pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {
			Object l; 
			Object r;
			//Is this checking for l and r instanceof really only doable here? The only other solution I can think of is by making many, many more visitors.
			switch (expression.op) {
			case PLUS:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.plus(l, r));
				}
				break;
			case MINUS:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.minus(l, r));
				}
				break;
			case MUL:
				
				//We don't need the second case in this situation since it's already inherently one of the correct solver types.
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) { //This satisfies the first of the conditions.
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.mult(l, r));
				}
				break;
			case DIV:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.div(l, r));
				}
				break;
			case REM:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.rem(l, r));
				}
				break;
			case AND:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.and(l, r));
				}
				break;
			case OR:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.or(l, r));
				}
				break;
			case XOR:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.xor(l, r));
				}
				break;
			case SHIFTR:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.shiftR(l, r));
				}
				break;
			case SHIFTUR:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.shiftUR(l, r));
				}
				break;
			case SHIFTL:
				r = stack.pop();
				l = stack.pop();
				if (l instanceof Long && r instanceof Long) {
					throw new RuntimeException("## Error: this is not a symbolic expression");
				} else {
					stack.push(pb.shiftL(l, r));
				}
				break;
			default:
				System.out.println("ProblemGeneralTranslator : unsupported operation " + expression.op);
				//Let's add the rest later. This should work for now.
				throw new RuntimeException();
			}
		} else {
			//Throw exception.
		}
	}

	@Override
	public void postVisit(BinaryLinearIntegerExpression expression) {
		Object l; 
		Object r;
		//Is this checking for l and r instanceof really only doable here? The only other solution I can think of is by making many, many more visitors.
		switch (expression.getOp()) {
		case PLUS:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.plus(l, r));
			}
			break;
		case MINUS:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.minus(l, r));
			}
			break;
		case MUL:
			
			//True question: Can BLIE expressions even do these sorts of operations in the first place? What exactly makes the multiplication of two
			//Object return values a BNLIE operation?
			//remove it.
			//If the solver is a solver capable of solving BNLIE expressions, then this should be able to handle cases where 
			//L and R are both not instances of Long.
			//Otherwise, it should fail.
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) { //This satisfies the first of the conditions.
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} if (!(l instanceof Long) && !(r instanceof Long)) {
				throw new RuntimeException("## Error: Binary Non Linear Operation");
			} else {
				stack.push(pb.mult(l, r));
			}
			break;
		case DIV:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} if (!(l instanceof Long) && !(r instanceof Long)) {
				if(pb instanceof ProblemCoral || pb instanceof ProblemZ3 || pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3BitVector ||
				          pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {
					stack.push(pb.div(l, r));
				} else {
					throw new RuntimeException("## Error: Binary Non Linear Operation");
				}
			} else {
				stack.push(pb.div(l, r));
			}
			break;
		case REM:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} if (!(l instanceof Long) && !(r instanceof Long)) {
				if(pb instanceof ProblemCoral || pb instanceof ProblemZ3 || pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3BitVector ||
				          pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {
					stack.push(pb.rem(l, r));
				} else {
					throw new RuntimeException("## Error: Binary Non Linear Operation");
				}
			} else {
				stack.push(pb.rem(l, r));
			}
			break;
		case AND:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.and(l, r));
			}
			break;
		case OR:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.or(l, r));
			}
			break;
		case XOR:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.xor(l, r));
			}
			break;
		case SHIFTR:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.shiftR(l, r));
			}
			break;
		case SHIFTUR:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.shiftUR(l, r));
			}
			break;
		case SHIFTL:
			r = stack.pop();
			l = stack.pop();
			if (l instanceof Long && r instanceof Long) {
				throw new RuntimeException("## Error: this is not a symbolic expression");
			} else {
				stack.push(pb.shiftL(l, r));
			}
			break;
		default:
			System.out.println("ProblemGeneralTranslator : unsupported operation " + expression.getOp());
			//Let's add the rest later. This should work for now.
			throw new RuntimeException();
		}
	}

	@Override
	public void postVisit(IntegerConstant integerConstant) {
		//Let's roll with this for now. Just adding the value to the stack.
		stack.add(integerConstant);
	}

	@Override
	public void postVisit(SymbolicInteger symbInt) {
		assert(symbInt._min >= Integer.MIN_VALUE && symbInt._max <= Integer.MAX_VALUE);
		Object dp_var = symIntegerVar.get(symbInt);
		
		if (dp_var == null) {
			dp_var = pb.makeIntVar(((SymbolicInteger)symbInt).getName(),((SymbolicInteger)symbInt)._min, ((SymbolicInteger)symbInt)._max);
			symIntegerVar.put((SymbolicInteger)symbInt, dp_var);
		}
		stack.add(dp_var);
	}



	@Override
	public void postVisit(MixedConstraint constraint) {
		//TODO: This case doesn't appear to be finished in PCParser. See: createDPMixedConstraint() in PCParser.java 
		//Though, I would imagine that it's easy to do here given how everything is being changed just by formatting it out like the previous constraint
		//postVisits.
	}
	
	@Override 
	public void postVisit(LogicalORLinearIntegerConstraints constraint) {
		//TODO: I'll get to this. This appears to be there to handle CNF style constraints, whatever those are.
	}
	
	@Override
	public void postVisit(NonLinearIntegerConstraint constraint) {
		
		//TODO: for NonLinearIntegerConstraint's accept method I used super() to fulfil the goal I was going for to check the left and right. Not sure if that was the correct way to go about it.
		//Spoiler alert: it's not.
		
		//Spoiler spoiler alert. Since this is extended from Constraint.java, it should just end up using the accept() method there instead of the terrible one I made for it.
		
		if(pb instanceof ProblemCoral || pb instanceof ProblemZ3|| pb instanceof ProblemZ3Optimize || 
				pb instanceof ProblemZ3BitVector || pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {
			//Insert how createDPNonLinearIntegerConstraint works here.
			//This is identical to RealConstraint, so can I just make one general case method for Constraints? I don't think that's the way to do it, but I'm not 100% on that.
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
		} else {
	        throw new RuntimeException("## Error: Non Linear Integer Constraint not handled " + constraint);
		}
	}
}
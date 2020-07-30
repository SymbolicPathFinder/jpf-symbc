package gov.nasa.jpf.symbc.numeric.solvers;

import java.util.Stack;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.visitors.ProblemGeneralVisitor;

public class ProblemGeneralTranslator {

	//Ignore this for now. This isn't being used.
	public static ProblemGeneral createInstance(Constraint c) {

		Expression e = null;

		while (c != null) {
			Translator translator = new Translator(); //Makes a new visitor.
			c.accept(translator);                     //This runs .accept() and eventually postVisit() on all of the expressions in the constraint
			//At this point, there needs to be a fully created solver-specific constraint on the stack within translator.
			//(for the first constraint that is)
			
			//expressions are added to the stack in Translator (symbolicReal or symbolicInt or SymbolicStrings only)
			Object tmp = translator.getExpression(); //This will get a peek() of the first expression added off the stack in Translator.

			if (e == null) {  //This is the first time through. so 'e' is this temp value created within translator
				e = tmp;      //Though, this is kinda assuming that tmp will actually be something.
			} else {
				//I need to make a generalized form of the operation here.
				e = new Operation(Operation.Operator.AND, e, tmp);
			}

			c = c.and;
		}

		//I think Instance is an instance of the solver for Green. The goal for me is to create an instance for a problemGeneral.
		Instance greenPC = new Instance(SymbolicInstructionFactory.greenSolver, null, e);
		return greenPC; //End goal is creating this.
	}
	
	
	private final static class Translator extends ProblemGeneralVisitor {

		private Stack<Expression> stack;

		public Translator() {
			stack = new Stack<Expression>();
		}

		public Expression getExpression() {
			return stack.peek();
		}

		@Override
		public void postVisit(Constraint constraint) { //This is called at the end of Constraint's accept() method
			Expression l;
			Expression r;
			switch (constraint.getComparator()) {
			case EQ:
				r = stack.pop();
				l = stack.pop();
				stack.push(new Operation(Operation.Operator.EQ, l, r));
				break;
			case NE:
				r = stack.pop();
				l = stack.pop();
				stack.push(new Operation(Operation.Operator.NE, l, r));
				break;
			case LT:
				r = stack.pop();
				l = stack.pop();
				stack.push(new Operation(Operation.Operator.LT, l, r));
				break;
			case LE:
				r = stack.pop();
				l = stack.pop();
				stack.push(new Operation(Operation.Operator.LE, l, r));
				break;
			case GT:
				r = stack.pop();
				l = stack.pop();
				stack.push(new Operation(Operation.Operator.GT, l, r));
				break;
			case GE:
				r = stack.pop();
				l = stack.pop();
				stack.push(new Operation(Operation.Operator.GE, l, r));
				break;
			}
		}

		@Override
		public void postVisit(BinaryLinearIntegerExpression expression) {
			Expression l;
			Expression r;
			switch (expression.getOp()) {
			case PLUS:
				r = stack.pop();
				l = stack.pop();
				stack.push(new Operation(Operation.Operator.ADD, l, r));
				break;
			case MINUS:
				r = stack.pop();
				l = stack.pop();
				stack.push(new Operation(Operation.Operator.SUB, l, r));
				break;
			case MUL:
				r = stack.pop();
				l = stack.pop();
				stack.push(new Operation(Operation.Operator.MUL, l, r));
				break;
			default:
				System.out.println("SolverTranslator : unsupported operation " + expression.getOp());
				throw new RuntimeException();
			}
		}

		@Override
		public void postVisit(IntegerConstant constant) {
			stack.push(new IntConstant((int)constant.value));
		}

		@Override
		public void postVisit(SymbolicInteger node) {
			assert(node._min>=Integer.MIN_VALUE && node._max<=Integer.MAX_VALUE);
			stack.push(new IntVariable(node.getName(), node, (int) node._min, (int) node._max));
		}

	}
}

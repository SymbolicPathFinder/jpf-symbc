package gov.nasa.jpf.symbc.numeric;

import gov.nasa.jpf.symbc.string.*;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.expr.Expression;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;


public class GreenToSPFTranslator extends Visitor{

	private boolean recent = true;
	//Add an extra boolean flag in order to keep track of whether a string of numeric expression was most recently added
	//This is used for valueOf()

	// We use this to determine whether a string constant is a regular expression.
	// PEND: This assumes that the left-hand side operand of MATCHES and NOMATCHES is never a constant!
	private boolean reg = false;

	private List<StringConstraint> constraints = null;
	private List<Constraint> constraints_numeric = null;
	private StringPathCondition spc = null;
	private Stack<StringExpression> new_expression;
	private Stack<IntegerExpression> int_exprs;
	private Stack<Constraint> constraints_numeric_stack = null;
	private Stack<StringConstraint> constraints_stack = null;

	public GreenToSPFTranslator(){
		new_expression = new Stack<StringExpression>();
		constraints = new LinkedList<StringConstraint>();
		constraints_numeric = new LinkedList<Constraint>();
		//I also need a stack for both?
		constraints_stack = new Stack<StringConstraint>();
		constraints_numeric_stack = new Stack<Constraint>();
		int_exprs = new Stack<IntegerExpression>();
	}

	public gov.nasa.jpf.symbc.numeric.Expression translate(Expression expression){
		try{
			expression.accept(this);
		}
		catch (VisitorException x){
			System.out.println("Should not be happening!!");
		}
		if(!int_exprs.empty())
			return int_exprs.pop();
		else if (!new_expression.empty())
			return new_expression.pop();
			else
				return null;
	}



	@Override
	public void postVisit(StringConstantGreen cons) {
		recent = false;
		if (reg) {
			StringConstant c = new StringConstant(cons.getValue(), true);
			new_expression.push(c);
		} else {
			StringConstant c = new StringConstant(cons.getValue());
			new_expression.push(c);
		}
	}


	@Override
	public void postVisit(StringVariable v) {
		recent = false;
		//SPF interprets CharAt as an integer. Check for this case.
		if (v instanceof CharAtVariable){
			recent = true;
			CharAtVariable v_char = (CharAtVariable) v;
			Integer lowerBound = v_char.getLowerBound();
			Integer upperBound = v_char.getUpperBound();
			StringExpression se = new_expression.pop();
			IntegerExpression ie = int_exprs.pop();
			SymbolicCharAtInteger var = new SymbolicCharAtInteger(v_char.toString(), lowerBound, upperBound, se, ie);
			int_exprs.push(var);
		}
		else{
			StringSymbolic var = new StringSymbolic(v.toString());
			new_expression.push(var);
		}
	}

	@Override
	public void postVisit(IntVariable v) {
		recent = true;
		Integer lowerBound = v.getLowerBound();
		Integer upperBound = v.getUpperBound();
		if (v instanceof LengthVariable){
			LengthVariable v_length = (LengthVariable) v;
			StringExpression se = new_expression.pop();
			SymbolicLengthInteger var = new SymbolicLengthInteger(v_length.toString(), lowerBound, upperBound, se);
			int_exprs.push(var);
		}
		else if (v instanceof IndexOfVariable){
			IndexOfVariable v_char = (IndexOfVariable) v;
			StringExpression ie = new_expression.pop();
			StringExpression se = new_expression.pop();
			SymbolicIndexOfInteger var = new SymbolicIndexOfInteger(v_char.toString(), lowerBound, upperBound, se,ie);
			int_exprs.push(var);
		}
		else if (v instanceof IndexOf2Variable){
			IndexOf2Variable v_char = (IndexOf2Variable) v;
			IntegerExpression id = int_exprs.pop();
			StringExpression ie = new_expression.pop();
			StringExpression se = new_expression.pop();
			SymbolicIndexOf2Integer var = new SymbolicIndexOf2Integer(v_char.toString(), lowerBound, upperBound, se,ie, id);
			int_exprs.push(var);
		}
		else if (v instanceof IndexOfCharVariable){
			IndexOfCharVariable v_char = (IndexOfCharVariable) v;
			StringExpression se = new_expression.pop();
			IntegerExpression ie = int_exprs.pop();
			SymbolicIndexOfCharInteger var = new SymbolicIndexOfCharInteger(v_char.toString(), lowerBound, upperBound, se,ie);
			int_exprs.push(var);
		}
		else if (v instanceof IndexOfChar2Variable){
			IndexOfChar2Variable v_char = (IndexOfChar2Variable) v;
			IntegerExpression id = int_exprs.pop();
			IntegerExpression ie = int_exprs.pop();
			StringExpression se = new_expression.pop();
			SymbolicIndexOfChar2Integer var = new SymbolicIndexOfChar2Integer(v_char.toString(), lowerBound, upperBound, se,ie, id);
			int_exprs.push(var);
		}
		else if (v instanceof LastIndexOfVariable){
			LastIndexOfVariable v_char = (LastIndexOfVariable) v;
			StringExpression ie = new_expression.pop();
			StringExpression se = new_expression.pop();
			SymbolicLastIndexOfInteger var = new SymbolicLastIndexOfInteger(v_char.toString(), lowerBound, upperBound, se,ie);
			int_exprs.push(var);
		}
		else if (v instanceof LastIndexOf2Variable){
			LastIndexOf2Variable v_char = (LastIndexOf2Variable) v;
			IntegerExpression id = int_exprs.pop();
			StringExpression ie = new_expression.pop();
			StringExpression se = new_expression.pop();
			SymbolicLastIndexOf2Integer var = new SymbolicLastIndexOf2Integer(v_char.toString(), lowerBound, upperBound, se,ie, id);
			int_exprs.push(var);
		}
		else if (v instanceof LastIndexOfCharVariable){
			LastIndexOfCharVariable v_char = (LastIndexOfCharVariable) v;
			StringExpression se = new_expression.pop();
			IntegerExpression ie = int_exprs.pop();
			SymbolicLastIndexOfCharInteger var = new SymbolicLastIndexOfCharInteger(v_char.toString(), lowerBound, upperBound, se,ie);
			int_exprs.push(var);
		}
		else if (v instanceof LastIndexOfChar2Variable){
			LastIndexOfChar2Variable v_char = (LastIndexOfChar2Variable) v;
			IntegerExpression id = int_exprs.pop();
			IntegerExpression ie = int_exprs.pop();
			StringExpression se = new_expression.pop();
			SymbolicLastIndexOfChar2Integer var = new SymbolicLastIndexOfChar2Integer(v_char.toString(), lowerBound, upperBound, se,ie, id);
			int_exprs.push(var);
		}
		else if (v instanceof IndexOfChar2Variable){
			IndexOfChar2Variable v_char = (IndexOfChar2Variable) v;
			IntegerExpression id = int_exprs.pop();
			IntegerExpression ie = int_exprs.pop();
			StringExpression se = new_expression.pop();
			SymbolicIndexOfChar2Integer var = new SymbolicIndexOfChar2Integer(v_char.toString(), lowerBound, upperBound, se,ie, id);
			int_exprs.push(var);
		}
		else{
			SymbolicInteger var = new SymbolicInteger(v.toString(), lowerBound, upperBound);
			int_exprs.push(var);
		}
	}

	@Override
	public void postVisit(IntConstant cons) {
		recent = true;
		IntegerConstant c = new IntegerConstant(cons.getValue());
		int_exprs.push(c);
	}

	@Override
	public void preVisit(Operation operation) {
		if(operation.getOperator() == Operation.Operator.MATCHES || operation.getOperator() == Operation.Operator.NOMATCHES) {
			reg = true;
		}
	}

	@Override
	public void postVisit(Operation operation) {

		Operation.Operator o = operation.getOperator();

		int arity = 0;
		for (Expression operand: operation.getOperands()){
			arity++;
		}

		StringExpression l = null;
		StringExpression r = null;
		StringExpression m = null;
		IntegerExpression e = null;
		IntegerExpression d = null;
		StringConstraint sc; 
		Constraint cn; 
		DerivedStringExpression se;
		BinaryLinearIntegerExpression ne;

		gov.nasa.jpf.symbc.numeric.Expression[] oprlist;
		switch (o) {
			/*case AND:
				if (!constraints_numeric_stack.empty()){
					constraints_numeric.add(constraints_numeric_stack.pop());
				}
				if (!constraints_numeric_stack.empty()){
					constraints_numeric.add(constraints_numeric_stack.pop());
				}
				if (!constraints_stack.empty()){
					constraints.add(constraints_stack.pop());
				}
				if (!constraints_stack.empty()){
					constraints.add(constraints_stack.pop());
				}
			break;
				
			case NOT:
			if (recent){
				cn = constraints_numeric_stack.pop();
				constraints_numeric_stack.push(cn.not());
			}
			else{
				sc = constraints_stack.pop();
				constraints_stack.push(sc.not());
			}
			break;
			case EQ:
			e = int_exprs.pop();
			d = int_exprs.pop();
			cn = new LinearIntegerConstraint(d, Comparator.EQ, e);
			constraints_numeric_stack.push(cn);
			break;
			case NE:
			e = int_exprs.pop();
			d = int_exprs.pop();
			cn = new LinearIntegerConstraint(d, Comparator.NE, e);
			constraints_numeric_stack.push(cn);
			break;
			case LT:
			e = int_exprs.pop();
			d = int_exprs.pop();
			cn = new LinearIntegerConstraint(d, Comparator.LT, e);
			constraints_numeric_stack.push(cn);
			break;
			case LE:
			e = int_exprs.pop();
			d = int_exprs.pop();
			cn = new LinearIntegerConstraint(d, Comparator.LE, e);
			constraints_numeric_stack.push(cn);
			break;
			case GT:
			e = int_exprs.pop();
			d = int_exprs.pop();
			cn = new LinearIntegerConstraint(d, Comparator.GT, e);
			constraints_numeric_stack.push(cn);
			break;
			case GE:
			e = int_exprs.pop();
			d = int_exprs.pop();
			cn = new LinearIntegerConstraint(d, Comparator.GE, e);
			constraints_numeric_stack.push(cn);
			break;
			case STARTSWITH:
			r = new_expression.pop();
			l = new_expression.pop();
			sc = new StringConstraint(l, StringComparator.STARTSWITH, r);
			constraints_stack.push(sc);
			break;
			case NOTSTARTSWITH:
			r = new_expression.pop();
			l = new_expression.pop();
			sc = new StringConstraint(l, StringComparator.NOTSTARTSWITH, r);
			constraints_stack.push(sc);
			break;
			case EQUALS:
			//Check if one of the operands is CharAt
			//In this case, translate the constraint as a numeric one for compatibility with SPF format
			//PENDING: test this case more aggressively. Assumes that if there is an integer child, it must be charAt
			if (!int_exprs.isEmpty()){
				//Assumption is that this only happens in the charAt case. 
				e = int_exprs.pop();
				if (!int_exprs.isEmpty()){
					d = int_exprs.pop();
					cn = new LinearIntegerConstraint(e, Comparator.EQ, d);
				}
				else{
					r = new_expression.pop();
					//We only handle the case where r is an integer constant. 
					if (r instanceof StringConstant){
						String string_val = ((StringConstant) r).value();
						//A character cannot be compared to a string of more than length one
						if (string_val.length() > 1){
							System.out.println("Green ABCTranslator : character is equal to string of length > 1!");
							throw new RuntimeException();	
						}
						Integer val = (int) string_val.charAt(0);
						IntegerConstant r_int = new IntegerConstant(val);
						//The order of right versus left is lost but does not matter. 
						cn = new LinearIntegerConstraint(e, Comparator.EQ,r_int);
					}
					else{
						System.out.println("Green ABCTranslator : unsupported charAt Case!");
						throw new RuntimeException();	
					}
					
				}
				constraints_numeric_stack.push(cn);
			}
			else{
				r = new_expression.pop();
				l = new_expression.pop();
				sc = new StringConstraint(l, StringComparator.EQUALS,r);
				constraints_stack.push(sc);
			}
			break;
			case NOTEQUALS:
			if (!int_exprs.isEmpty()){
				//Assumption is that this only happens in the charAt case. 
				e = int_exprs.pop();
				if (!int_exprs.isEmpty()){
					d = int_exprs.pop();
					cn = new LinearIntegerConstraint(e, Comparator.NE, d);
				}
				else{
					r = new_expression.pop();
					//We only handle the case where r is an integer constant. 
					if (r instanceof StringConstant){
						String string_val = ((StringConstant) r).value();
						//A character cannot be compared to a string of more than length one
						if (string_val.length() > 1){
							System.out.println("Green ABCTranslator : character is equal to string of length > 1!");
							throw new RuntimeException();	
						}
						Integer val = (int) string_val.charAt(0);
						IntegerConstant r_int = new IntegerConstant(val);
						//The order of right versus left is lost but does not matter. 
						cn = new LinearIntegerConstraint(e, Comparator.NE,r_int);
					}
					else{
						System.out.println("Green ABCTranslator : unsupported charAt Case!");
						throw new RuntimeException();	
					}
					
				}
				constraints_numeric_stack.push(cn);
			}
			else{
				r = new_expression.pop();
				l = new_expression.pop();
				sc = new StringConstraint(l, StringComparator.NOTEQUALS,r);
				constraints_stack.push(sc);
			}
			break;
			case CONTAINS:
			r = new_expression.pop();
			l = new_expression.pop();
			sc = new StringConstraint(l, StringComparator.CONTAINS,r);
			constraints_stack.push(sc);
			break;
			case NOTCONTAINS:
			r = new_expression.pop();
			l = new_expression.pop();
			sc = new StringConstraint(l, StringComparator.NOTCONTAINS,r);
			constraints_stack.push(sc);
			break;			
			case ENDSWITH:
			r = new_expression.pop();
			l = new_expression.pop();
			sc = new StringConstraint(l, StringComparator.ENDSWITH,r);
			constraints_stack.push(sc);
			break;
			case NOTENDSWITH:
			r = new_expression.pop();
			l = new_expression.pop();
			sc = new StringConstraint(l, StringComparator.NOTENDSWITH,r);
			constraints_stack.push(sc);
			break;
			//PENDING: Adding in translation for regular expression constraints back to SPF.
			//Check to ensure that construction is compatible with SPF. 
			case MATCHES:
			reg = false;
			r = new_expression.pop();
			l = new_expression.pop();
			sc = new StringConstraint(l, StringComparator.MATCHES,r);
			constraints_stack.push(sc);
			break;	
			case NOMATCHES:
			reg = false;
			r = new_expression.pop();
			l = new_expression.pop();
			sc = new StringConstraint(l, StringComparator.NOMATCHES,r);
			constraints_stack.push(sc);
			break;	*/
			case ADD:
			recent = true; 
			e = int_exprs.pop();
			d = int_exprs.pop();
			ne = new BinaryLinearIntegerExpression(e, Operator.PLUS, d);
			int_exprs.push(ne);
			break;
			case SUB:
			recent = true; 
			e = int_exprs.pop();
			d = int_exprs.pop();
			ne = new BinaryLinearIntegerExpression(e, Operator.MINUS, d);
			int_exprs.push(ne);
			break;
			case MUL:
			recent = true; 
			e = int_exprs.pop();
			d = int_exprs.pop();
			ne = new BinaryLinearIntegerExpression(e, Operator.MUL, d);
			int_exprs.push(ne);
			break;
			case DIV:
			recent = true; 
			e = int_exprs.pop();
			d = int_exprs.pop();
			ne = new BinaryLinearIntegerExpression(e, Operator.DIV, d);
			int_exprs.push(ne);
			break;
			case CONCAT:
			recent = false; 
			r = new_expression.pop();
			l = new_expression.pop();
			se = new DerivedStringExpression(l, StringOperator.CONCAT,r);
			new_expression.push(se);
			break;
			case TRIM:
			recent = false; 
			r = new_expression.pop();
			se = new DerivedStringExpression(StringOperator.TRIM,r);
			new_expression.push(se);
			break;
			case REPLACE:
			recent = false;
			r = new_expression.pop();
			l = new_expression.pop();
			m = new_expression.pop();
			oprlist = new StringExpression[3];
			oprlist[0] = m;
			oprlist[1] = l;
			oprlist[2] = r;
			se = new DerivedStringExpression(StringOperator.REPLACE, oprlist);
			new_expression.push(se);
			break;
			case REPLACEFIRST:
			recent = false; 
			r = new_expression.pop();
			l = new_expression.pop();
			m = new_expression.pop();
			oprlist = new StringExpression[3];
			oprlist[0] = m;
			oprlist[1] = l;
			oprlist[2] = r;
			se = new DerivedStringExpression(StringOperator.REPLACEFIRST, oprlist);
			new_expression.push(se);
			break;
			case SUBSTRING:
			recent = false;
			//System.out.println("in case substring!");
			l = new_expression.pop();
			e = int_exprs.pop();
			if (arity == 3){
				d = int_exprs.pop();
				oprlist = new gov.nasa.jpf.symbc.numeric.Expression[3];
				oprlist[0] = l;
				oprlist[1] = d;
				oprlist[2] = e;
				se = new DerivedStringExpression(StringOperator.SUBSTRING, oprlist);
			}
			else{
				oprlist = new gov.nasa.jpf.symbc.numeric.Expression[2];
				oprlist[0] = l;
				oprlist[1] = e;
				se = new DerivedStringExpression(StringOperator.SUBSTRING, oprlist);
			}
			new_expression.push(se);
			break;
			case VALUEOF:
				oprlist = new gov.nasa.jpf.symbc.numeric.Expression[1];
				if(recent) {
					// int expr stack is nonempty => operand is an int expr
					//System.out.println("********************************* int expr stack is nonempty => operand is an int expr");
					e = int_exprs.pop();
					oprlist[0] = e;
				} else {
					// int expr stack is empty => operand is a string expr
					//System.out.println("********************************* int expr stack is empty => operand is a string expr");
					l = new_expression.pop();
					oprlist[0] = l;
				}
				se = new DerivedStringExpression(StringOperator.VALUEOF, oprlist);
				new_expression.push(se);
				recent = false; 
			break;		
			default:
			break;

		}
	}
}




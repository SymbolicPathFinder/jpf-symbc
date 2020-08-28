/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */

package gov.nasa.jpf.symbc.numeric.visitors;

import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.BinaryNonLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.BinaryRealExpression;
import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor2;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.MathRealExpression;
import gov.nasa.jpf.symbc.numeric.PCParser;
import gov.nasa.jpf.symbc.numeric.RealConstant;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;

/**
 * This class does the general parsing for the various types of expressions parsed within the PCParser class.
 * Extend from this class with a type of constraint, where you create visit() methods to handle passing various
 * different types of constraints to the solver. This class extends from ConstraintExpressionVisitor2, which
 * itself extends from ConstraintExpressionVisitor, where preVisit() and postVisit() methods were created for 
 * each of the different classes.
 * 
 * In order to handle new types of constraints, create a new visitor class for the constraint and extend from
 * this class. Have a visit() method overridden inside your new class for the constraint, and handle the parsing
 * of the constraint within the visitor. You'll also probably have to create an accept() method within the 
 * relevant constraint method, but that shouldn't be hard either. If you should need to change the functionality
 * of how any Expressions are parsed, just override the methods below within your newly created visitor and handle
 * the expression parsing there.
 * 
 * @author Carson Smith
 */
public class ProblemGeneralVisitor extends ConstraintExpressionVisitor2 {

	/**
	 * The ProblemGeneral object that the visitor system will be posting to and using.
	 */
	static ProblemGeneral pb;

	/**
	 * CONSTRUCTOR: Creates a ProblemGeneralVisitor object
	 * @param pb - The ProblemGeneral object you're initializing with.
	 */
	public ProblemGeneralVisitor(ProblemGeneral pb) {
		ProblemGeneralVisitor.pb = pb;
	}

	//IntegerConstant Method
	@Override
	public Long visit(IntegerConstant integerConstant) {
		Long value = integerConstant.value;
		return value;
	}

	//SymbolicInt Method
	@Override
	public Object visit(SymbolicInteger symbInt) {
		Object dp_var = PCParser.symIntegerVar.get(symbInt);

		if (dp_var == null) {
			dp_var = pb.makeIntVar(symbInt.getName(),symbInt._min, symbInt._max);
			PCParser.symIntegerVar.put(symbInt, dp_var);
		}
		return dp_var;
	}

	//RealConstant method
	@Override
	public Double visit(RealConstant realConstant) {
		Double value = realConstant.value;
		return value;
	}

	//SymbolicReal Method
	@Override
	public Object visit(SymbolicReal symbReal) {
		Object dp_var = PCParser.symRealVar.get(symbReal);

		if (dp_var == null) {
			dp_var = pb.makeRealVar(symbReal.getName(), symbReal._min, symbReal._max);
			PCParser.symRealVar.put(symbReal, dp_var);
		}
		return dp_var;
	}

	//MathRealExpression visitor
	@Override
	public Object visit(MathRealExpression expression) {
		assert expression.arg1 != null;

		Object leftExpr = null;
		Object rightExpr = null;

		leftExpr = expression.arg1.accept(this); //Visit arg1 (This should always happen)

		if (expression.arg2 != null) {
			rightExpr = expression.arg2.accept(this); //Visit arg2 (if needed)
		}

		switch(expression.op){
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
			throw new RuntimeException("## Error: Expression " + expression);
		}
	}

	//BinaryRealExpression visitor
	@Override
	public Object visit(BinaryRealExpression expression) {

		RealExpression left = expression.getLeft();
		RealExpression right = expression.getRight();

		Object lExpr = left.accept(this); //Visit the left
		Object rExpr = right.accept(this); //Visit the right

		if(lExpr instanceof Double && rExpr instanceof Double) {
			return parseBRE_DD(((Double) lExpr), expression, ((Double) rExpr));
		} else if(lExpr instanceof Double) {
			return parseBRE_DO(((Double) lExpr), expression, rExpr);
		} else if(rExpr instanceof Double) {
			return parseBRE_OD(lExpr, expression, ((Double) rExpr));
		} else {
			return parseBRE_OO(lExpr, expression, rExpr);
		}
	}

	//BinaryRealExpression Parsing Methods
	private Object parseBRE_DD(Double lExpr, BinaryRealExpression expression, Double rExpr) {
		throw new RuntimeException("## Error: This is not a symbolic expression");
	}

	private Object parseBRE_DO(Double lExpr, BinaryRealExpression expression, Object rExpr) {
		double lExpr2 = lExpr.doubleValue();
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

	private Object parseBRE_OD(Object lExpr, BinaryRealExpression expression, Double rExpr) {
		double rExpr2 = rExpr.doubleValue();
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

	private Object parseBRE_OO(Object lExpr, BinaryRealExpression expression, Object rExpr) {
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

	//BinaryLinearIntegerExpression Visitor
	@Override
	public Object visit(BinaryLinearIntegerExpression expression) {

		IntegerExpression left = expression.getLeft();
		IntegerExpression right = expression.getRight();

		Object lExpr = left.accept(this);
		Object rExpr = right.accept(this);

		if(lExpr instanceof Long && rExpr instanceof Long) {
			return parseBLIE_LL(((Long) lExpr), expression, ((Long) rExpr));
		} else if(lExpr instanceof Long) {
			return parseBLIE_LO(((Long) lExpr), expression, rExpr);
		} else if(rExpr instanceof Long) {
			return parseBLIE_OL(lExpr, expression, ((Long) rExpr));
		} else {
			return parseBLIE_OO(lExpr, expression, rExpr);
		}
	}

	//BinaryLinearIntegerExpression Parsing Methods
	private Object parseBLIE_LL(Long lExpr, BinaryLinearIntegerExpression expression, Long rExpr) {
		throw new RuntimeException("## Error: this is not a symbolic expression");
	}

	private Object parseBLIE_OL(Object lExpr, BinaryLinearIntegerExpression expression, Long rExpr) {
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

	private Object parseBLIE_LO(Long lExpr, BinaryLinearIntegerExpression expression, Object rExpr) {
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

	private Object parseBLIE_OO(Object lExpr, BinaryLinearIntegerExpression expression, Object rExpr) {
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

	//BinaryNonLinearIntegerExpression Visitor
	@Override
	public Object visit(BinaryNonLinearIntegerExpression expression) {

		if(pb.isNonLinearSolver()) { //Z3, Z3 derivatives, or Coral
			IntegerExpression left = expression.left;
			IntegerExpression right = expression.right;

			Object lExpr = left.accept(this);  //Visit the left
			Object rExpr = right.accept(this); //Visit the right

			if(lExpr instanceof Long && rExpr instanceof Long) {
				return parseBNLIE_LL(((Long) lExpr), expression, ((Long) rExpr));
			} else if(lExpr instanceof Long) {
				return parseBNLIE_LO(((Long) lExpr), expression, rExpr);
			} else if(rExpr instanceof Long) {
				return parseBNLIE_OL(lExpr, expression, ((Long) rExpr));
			} else {
				return parseBNLIE_OO(lExpr, expression, rExpr);
			}
		} else {
			//It's not a solver that can solveBinaryNonLinearIntegerExpressions.
			throw new RuntimeException("Selected solver type cannot solve BinaryNonLinearIntegerExpressions");
		}
	}

	//BinaryNonLinearIntegerExpression Parsing Methods
	private Object parseBNLIE_LL(Long lExpr, BinaryNonLinearIntegerExpression expression, Long rExpr) {
		throw new RuntimeException("## Error: this is not a symbolic expression");
	}

	private Object parseBNLIE_OL(Object lExpr, BinaryNonLinearIntegerExpression expression, Long rExpr) {
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

	private Object parseBNLIE_LO(Long lExpr, BinaryNonLinearIntegerExpression expression, Object rExpr) {
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

	private Object parseBNLIE_OO(Object lExpr, BinaryNonLinearIntegerExpression expression, Object rExpr) {

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

}
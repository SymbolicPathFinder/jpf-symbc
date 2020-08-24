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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import gov.nasa.jpf.symbc.arrays.ArrayConstraint;
import gov.nasa.jpf.symbc.arrays.ArrayExpression;
import gov.nasa.jpf.symbc.arrays.InitExpression;
import gov.nasa.jpf.symbc.arrays.RealArrayConstraint;
import gov.nasa.jpf.symbc.arrays.RealStoreExpression;
import gov.nasa.jpf.symbc.arrays.SelectExpression;
import gov.nasa.jpf.symbc.arrays.StoreExpression;
import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.BinaryNonLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.BinaryRealExpression;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor2;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
import gov.nasa.jpf.symbc.numeric.MathRealExpression;
import gov.nasa.jpf.symbc.numeric.MinMax;
import gov.nasa.jpf.symbc.numeric.MixedConstraint;
import gov.nasa.jpf.symbc.numeric.NonLinearIntegerConstraint;
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

/**
 * This class does the general parsing for the various types of expressions parsed within the PCParser class.
 * Extend from this class with a type of constraint, where you create visit() methods to handle passing various
 * different types of constraints to the solver. This class extends from ConstraintExpressionVisitor2, which
 * itself extends from ConstraintExpressionVisitor, where preVisit() and postVisit() methods were created for 
 * each of the different classes.
 * 
 * @author Carson Smith
 */
public class ProblemGeneralVisitor extends ConstraintExpressionVisitor2 {

	//Idea: Splitting constraints based on LinearIntegerConstraintsVisitor in it's own file. Make the visitor pattern itself more modular.

	//They would decend from a common abstract ProblemGeneral Solver class where general case methods for handling the different 
	//constraints would be, but the methods would be overridden in the solver. Expression methods are all in an asbstract class. Further different types
	//of constraint solvers are in the other types of solvers that extend and override from that.

	//Static-ness of the class design (regarding tempVars and how this class will work with PCParser in the end)

	//Regression

	//NonLinearIntegerConstraints don't have an explicit accept() method. Does that fuck everything up?
	//Can I avoid using all of those explicit accept() methods now that I've brought the branching behavior into visit() methods?

	//Do stuff in visit()...
	//Return pb in postVisit() so accept() methods are better looking? I could avoid returning a boolean in general by having a global
	//value that gets returned for constraints. For the Objects though, I'd need to use a stack.
	
	//How to handle tempvars outside of PCParser.

	static public Map<SymbolicReal, Object>	symRealVar = new HashMap<SymbolicReal,Object>(); // a map between symbolic real variables and DP variables
	static Map<SymbolicInteger,Object>	symIntegerVar = new HashMap<SymbolicInteger,Object>();

	static int tempVars;

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
		tempVars = 0;
	}

	public int getTempVars() {
		return tempVars;
	}

	public static Map<SymbolicReal, Object> getSymRealVar() {
		return symRealVar;
	}

	public static Map<SymbolicInteger, Object> getSymIntVar() {
		return symIntegerVar;
	}

	//------------------------------------------------------------------------------------------------------------------------------------------

	//Integer Method
	@Override
	public Long visit(IntegerConstant integerConstant) {
		Long value = integerConstant.value;
		return value;
	}

	//SymbInt Method
	@Override
	public Object visit(SymbolicInteger symbInt) {
		assert(symbInt._min >= Integer.MIN_VALUE && symbInt._max <= Integer.MAX_VALUE);
		Object dp_var = symIntegerVar.get(symbInt);

		if (dp_var == null) {
			dp_var = pb.makeIntVar(((SymbolicInteger)symbInt).getName(),((SymbolicInteger)symbInt)._min, ((SymbolicInteger)symbInt)._max);
			symIntegerVar.put((SymbolicInteger)symbInt, dp_var);
		}
		return dp_var;
	}

	//Real method
	@Override
	public Double visit(RealConstant realConstant) {
		Double value = realConstant.value;
		return value;
	}

	//SymbReal Method
	@Override
	public Object visit(SymbolicReal symbReal) {
		//TODO: This assertion statement completely messes with everything for some reason when double max and mins are specified.
		//I'll have to look into it.
		//assert(symbReal._min >= Double.MIN_VALUE && symbReal._max <= Double.MAX_VALUE);
		Object dp_var = symRealVar.get(symbReal);

		if (dp_var == null) {
			dp_var = pb.makeRealVar(((SymbolicReal)symbReal).getName(), ((SymbolicReal)symbReal)._min, ((SymbolicReal)symbReal)._max);
			symRealVar.put((SymbolicReal)symbReal, dp_var);
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

	//RealConstraint visitor
	@Override
	public boolean visit(RealConstraint constraint) {

		RealExpression left = constraint.getLeft();
		RealExpression right = constraint.getRight();

		Object lExpr = left.accept(this);
		Object rExpr = right.accept(this);

		if(lExpr instanceof Double && rExpr instanceof Double) {
			return parseRC_DD(((Double) lExpr), constraint, ((Double) rExpr));
		} else if(lExpr instanceof Double) {
			return parseRC_DO(((Double) lExpr), constraint, rExpr);
		} else if(rExpr instanceof Double) {
			return parseRC_OD(lExpr, constraint, ((Double) rExpr));
		} else {
			return parseRC_OO(lExpr, constraint, rExpr);
		}
	}

	//RealConstraint Parsing Methods
	public boolean parseRC_OO(Object left, RealConstraint constraint, Object right) {
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

	public boolean parseRC_OD(Object left, RealConstraint constraint, Double right) {
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

	public boolean parseRC_DO(Double left, RealConstraint constraint, Object right) {
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

	public boolean parseRC_DD(Double left, RealConstraint constraint, Double right) {
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
	public Object parseBRE_DD(Double lExpr, BinaryRealExpression expression, Double rExpr) {
		throw new RuntimeException("## Error: this is not a symbolic expression");
	}

	public Object parseBRE_DO(Double lExpr, BinaryRealExpression expression, Object rExpr) {
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

	public Object parseBRE_OD(Object lExpr, BinaryRealExpression expression, Double rExpr) {
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

	public Object parseBRE_OO(Object lExpr, BinaryRealExpression expression, Object rExpr) {
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

	//LinearIntegerConstraint visitor
	@Override
	public boolean visit(LinearIntegerConstraint constraint) {

		Object lExpr = constraint.getLeft().accept(this);
		Object rExpr = constraint.getRight().accept(this);

		if(lExpr instanceof Long && rExpr instanceof Long) {
			return parseLIC_LL(((Long) lExpr), constraint, ((Long) rExpr));
		} else if(lExpr instanceof Long) {
			return parseLIC_LO(((Long) lExpr), constraint, rExpr);
		} else if(rExpr instanceof Long) {
			return parseLIC_OL(lExpr, constraint, ((Long) rExpr));
		} else {
			return parseLIC_OO(lExpr, constraint, rExpr);
		}
	}

	//LinearIntegerConstraint Parsing Methods
	public boolean parseLIC_LL(Long left, LinearIntegerConstraint constraint, Long right) {
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

	public boolean parseLIC_LO(Long left, LinearIntegerConstraint constraint, Object right) {
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

	public boolean parseLIC_OL(Object left, LinearIntegerConstraint constraint, Long right) {
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

	public boolean parseLIC_OO(Object left, LinearIntegerConstraint constraint, Object right) {
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

	//NonLinearIntegerConstraint Visitor
	@Override
	public boolean visit(NonLinearIntegerConstraint constraint) {
		//TODO: Get rid of this terrible instanceof statement for solver types.
		//Make a true/false for NLIC supported pb's and just check that.
		if(pb instanceof ProblemCoral || pb instanceof ProblemZ3|| pb instanceof ProblemZ3Optimize || 
				pb instanceof ProblemZ3BitVector || pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {

			Object lExpr = constraint.getLeft().accept(this);
			Object rExpr = constraint.getRight().accept(this);

			if(lExpr instanceof Long && rExpr instanceof Long) {
				return parseNLIC_LL(((Long) lExpr), constraint, ((Long) rExpr));
			} else if(lExpr instanceof Long) {
				return parseNLIC_LO(((Long) lExpr), constraint, rExpr);
			} else if(rExpr instanceof Long) {
				return parseNLIC_OL(lExpr, constraint, ((Long) rExpr));
			} else {
				return parseNLIC_OO(lExpr, constraint, rExpr);
			}

		} else {
			throw new RuntimeException("## Error: Non Linear Integer Constraint not handled " + constraint);
		}
	}

	//NonLinearIntegerConstraint Parsing Methods
	public boolean parseNLIC_LL(Long left, NonLinearIntegerConstraint constraint, Long right) {
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

	public boolean parseNLIC_LO(Long left, NonLinearIntegerConstraint constraint, Object right) {
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

	public boolean parseNLIC_OL(Object left, NonLinearIntegerConstraint constraint, Long right) {
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

	public boolean parseNLIC_OO(Object left, NonLinearIntegerConstraint constraint, Object right) {
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
	public Object parseBLIE_LL(Long lExpr, BinaryLinearIntegerExpression expression, Long rExpr) {
		throw new RuntimeException("## Error: this is not a symbolic expression");
	}

	public Object parseBLIE_OL(Object lExpr, BinaryLinearIntegerExpression expression, Long rExpr) {
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

	public Object parseBLIE_LO(Long lExpr, BinaryLinearIntegerExpression expression, Object rExpr) {
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

	public Object parseBLIE_OO(Object lExpr, BinaryLinearIntegerExpression expression, Object rExpr) {
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

		//TODO: Get rid of this terrible instanceof statement for solver types.
		//Make a true/false for non-linear supported pb's and just check that.
		if(pb instanceof ProblemCoral || pb instanceof ProblemZ3 || pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3BitVector ||
				pb instanceof ProblemZ3Incremental || pb instanceof ProblemZ3BitVectorIncremental) {

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
	public Object parseBNLIE_LL(Long lExpr, BinaryNonLinearIntegerExpression expression, Long rExpr) {
		throw new RuntimeException("## Error: this is not a symbolic expression");
	}

	public Object parseBNLIE_OL(Object lExpr, BinaryNonLinearIntegerExpression expression, Long rExpr) {
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

	public Object parseBNLIE_LO(Long lExpr, BinaryNonLinearIntegerExpression expression, Object rExpr) {
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

	public Object parseBNLIE_OO(Object lExpr, BinaryNonLinearIntegerExpression expression, Object rExpr) {

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

	//MixedConstraint Visitor
	@Override
	public boolean visit(MixedConstraint constraint) {
		RealExpression left = constraint.getLeft();
		IntegerExpression right = constraint.getRight();
		if(left instanceof SymbolicReal && right instanceof SymbolicInteger) {
			return parseMC_RI(((SymbolicReal) left), constraint, ((SymbolicInteger) right));
		} else if(left instanceof SymbolicReal) {
			return parseMC_RO(((SymbolicReal) left), constraint, right);
		} else if(right instanceof SymbolicInteger) {
			return parseMC_OI(left, constraint, ((SymbolicInteger) right));
		} else {
			return parseMC_OO(left, constraint, right);
		}
	}

	//MixedConstraint Parsing Methods
	public boolean parseMC_OO(RealExpression left, MixedConstraint constraint, IntegerExpression right) {
		//However, instead of a false assert, it'd probably be better to throw a Runtime Exception of some sort.
		assert(false); //This should be unreachable according to the code's author.
		return true;
	}

	public boolean parseMC_OI(RealExpression left, MixedConstraint constraint, SymbolicInteger right) {
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

	public boolean parseMC_RO(SymbolicReal left, MixedConstraint constraint, IntegerExpression right) {
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

	public boolean parseMC_RI(SymbolicReal left, MixedConstraint constraint, SymbolicInteger right) {
		assert (constraint.getComparator() == Comparator.EQ);

		Object l = left.accept(this);
		Object r = right.accept(this);

		pb.post(pb.mixed(l, r));

		return true;
	}

	//LogicalORLinearIntegerConstraints Visitor
	@Override 
	public boolean visit(LogicalORLinearIntegerConstraints constraint) {

		List<Object> orList = new ArrayList<Object>();

		for (LinearIntegerConstraint cRef: constraint.getList()) {
			Object cc;
			Object lRef = cRef.getLeft().accept(this);
			Object rRef = cRef.getRight().accept(this);
			if(lRef instanceof Long && rRef instanceof Long) {
				cc = parseLOLIC_LL((Long)lRef, cRef.getComparator(), (Long)rRef);
			} else if(lRef instanceof Long) {
				cc = parseLOLIC_LO((Long)lRef, cRef.getComparator(), rRef);
			} else if(rRef instanceof Long) {
				cc = parseLOLIC_OL(lRef, cRef.getComparator(), (Long)rRef);
			} else {
				cc = parseLOLIC_OO(lRef, cRef.getComparator(), rRef);
			}
			orList.add(cc);
		}

		//System.out.println("[SymbolicConstraintsGeneral] orList: " + orList.toString());
		if (orList.size() == 0) {
			return true;
		}
		Object constraint_array[] = new Object[orList.size()];
		orList.toArray(constraint_array);

		pb.postLogicalOR(constraint_array);

		return true;
	}

	//LogicalORLinearIntegerConstraints Parsing Methods
	public Object parseLOLIC_LL(Long left, Comparator comp, Long right) {
		long left2 = left.longValue();
		long right2 = right.longValue();
		switch(comp){
		case EQ:
			if (left2 == right2) {
				return true;
			}
			break;
		case NE:
			if (left2 != right2) {
				return true;
			}
			break;
		case LT:
			if (left2 < right2) {
				return true;
			}
			break;
		case LE:
			if (left2 <= right2) {
				return true;
			}
			break;
		case GT:
			if (left2 > right2) {
				return true;
			}
			break;
		case GE:
			if (left2 >= right2) {
				return true;
			}
			break;
		}
		return false;
	}

	public Object parseLOLIC_LO(Long left, Comparator comp, Object right) {

		long leftConst = left.longValue(); //This could technically be removed right?

		Object tempVar = pb.makeIntVar("mytemp" + tempVars, MinMax.getVarMinInt(""), MinMax.getVarMaxInt("")); 
		tempVars++;
		pb.post(pb.eq(tempVar, right));

		switch(comp){
		case EQ:
			return pb.eq(leftConst, tempVar);
		case NE:
			return pb.neq(leftConst, tempVar);
		case LT:
			return pb.lt(leftConst, tempVar);
		case LE:
			return pb.leq(leftConst, tempVar);
		case GT:
			return pb.gt(leftConst, tempVar);
		case GE:
			return pb.geq(leftConst, tempVar);
		default:
			throw new RuntimeException("No valid comparator"); //Shouldn't be reachable
		}
	}

	public Object parseLOLIC_OL(Object left, Comparator comp, Long right) {
		long rightConst = right.longValue(); //This could technically be removed right?
		Object tempVar = pb.makeIntVar("mytemp" + tempVars, MinMax.getVarMinInt(""), MinMax.getVarMaxInt("")); 
		tempVars++;
		pb.post(pb.eq(tempVar, left));

		switch(comp){
		case EQ:
			return pb.eq(tempVar, rightConst);
		case NE:
			return pb.neq(tempVar, rightConst);
		case LT:
			return pb.lt(tempVar, rightConst);
		case LE:
			return pb.leq(tempVar, rightConst);
		case GT:
			return pb.gt(tempVar, rightConst);
		case GE:
			return pb.geq(tempVar, rightConst);
		default:
			throw new RuntimeException("No valid comparator"); //Shouldn't be reachable
		}
	}

	public Object parseLOLIC_OO(Object left, Comparator comp, Object right) {

		Object tempVar1 = pb.makeIntVar("mytemp" + tempVars, MinMax.getVarMinInt(""), MinMax.getVarMaxInt(""));
		tempVars++;
		Object tempVar2 = pb.makeIntVar("mytemp" + tempVars, MinMax.getVarMinInt(""), MinMax.getVarMaxInt(""));
		tempVars++;
		pb.post(pb.eq(tempVar1, left));
		pb.post(pb.eq(tempVar2, right));

		switch(comp){
		case EQ:
			return pb.eq(tempVar1, tempVar2);
		case NE:
			return pb.neq(tempVar1, tempVar2);
		case LT:
			return pb.lt(tempVar1, tempVar2);
		case LE:
			return pb.leq(tempVar1, tempVar2);
		case GT:
			return pb.gt(tempVar1,tempVar2);
		case GE:
			return pb.geq(tempVar1, tempVar2);
		default:
			throw new RuntimeException("No valid comparator"); //Shouldn't be reachable
		}
	}

	//ArrayConstraint Visitor
	@Override
	public boolean visit(ArrayConstraint constraint) {
		//TODO: Look into getting rid of this instance of for pb types as well.
		if (pb instanceof ProblemZ3|| pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3Incremental || 
				pb instanceof ProblemZ3BitVector || pb instanceof ProblemZ3BitVectorIncremental) {
			Object left = constraint.getLeft();
			Object right = constraint.getRight();

			if(left instanceof SelectExpression) {
				parseAC_Select(((SelectExpression) left), constraint, ((IntegerExpression) right));
			} else if(left instanceof StoreExpression) {
				parseAC_Store((StoreExpression) left, constraint, ((ArrayExpression) right));
			} else if(left instanceof InitExpression) {
				parseAC_Init(((InitExpression) left), constraint);
			} else { 
				throw new RuntimeException("ArrayConstraint is not select or store or init");
			}
			return true;
		} else {
			throw new RuntimeException("## Error : Array constraints only handled by z3. Try specifying a z3 instance as symbolic.dp");
		}
	}

	//ArrayConstraint Parsing Methods
	public void parseAC_Select(SelectExpression selex, ArrayConstraint ac, IntegerExpression sel_right) {
		assert selex != null;
		assert sel_right != null;

		ArrayExpression ae = (ArrayExpression) selex.arrayExpression;
		Object selexRef = selex.indexExpression.accept(this);  //Visit the selex
		Object sel_rightRef = sel_right.accept(this);          //Visit the sel_right
		switch(ac.getComparator()) {
		case EQ:
			//If the selexRef is a Long, make an intConst
			if(selexRef instanceof Long) {
				selexRef = pb.makeIntConst(((Long)selexRef).longValue());
			}

			if(sel_rightRef instanceof Long) {
				sel_rightRef = pb.makeIntConst(((Long)sel_rightRef).longValue());
			}

			//Post everything to the solver.
			pb.post(pb.eq(pb.select(pb.makeArrayVar(ae.getName()), selexRef), sel_rightRef));
		case NE:
			// The array constraint is a select

			pb.post(pb.neq(pb.select(pb.makeArrayVar(ae.getName()), selexRef), sel_rightRef));
			break;
		default:
			throw new RuntimeException("ArrayConstraint is not select or store");
		}
	}

	public void parseAC_Store(StoreExpression stoex, ArrayConstraint ac, ArrayExpression sto_right) {
		assert stoex != null;
		assert sto_right != null;

		ArrayExpression ae = (ArrayExpression) stoex.arrayExpression;
		ArrayExpression newae = (ArrayExpression) sto_right;
		Object stoexRef = stoex.indexExpression.accept(this);  //Visit the stoex
		Object stoexValRef = stoex.value.accept(this);         //Visit the stoex value
		switch(ac.getComparator()) {
		case EQ:

			//If the selexRef is a Long, make an intConst
			if(stoexRef instanceof Long) {
				stoexRef = pb.makeIntConst(((Long)stoexRef).longValue());
			}

			if(stoexValRef instanceof Long) {
				stoexValRef = pb.makeIntConst(((Long)stoexValRef).longValue());
			}

			pb.post(pb.eq(pb.store(pb.makeArrayVar(ae.getName()), stoexRef, stoexValRef), pb.makeArrayVar(newae.getName())));
		case NE:

			pb.post(pb.neq(pb.store(pb.makeArrayVar(ae.getName()), stoexRef, stoexValRef), newae));
			break;
		default:
			throw new RuntimeException("ArrayConstraint is not select or store");
		}
	}

	public void parseAC_Init(InitExpression initex, ArrayConstraint ac) {
		assert initex != null;
		switch(ac.getComparator()) {
		case EQ:
			ArrayExpression ae = (ArrayExpression) initex.arrayExpression;
			IntegerConstant init_value = new IntegerConstant(initex.isRef? -1 : 0);
			pb.post(pb.init_array(pb.makeArrayVar(ae.getName()), pb.makeIntConst(init_value.value)));
			break;
		case NE:
			throw new RuntimeException("InitExpression doesn't work for NE comparator");
		default:
			throw new RuntimeException("ArrayConstraint is not select or store");
		}
	}

	//RealArrayConstraint Visitor
	@Override
	public boolean visit(RealArrayConstraint constraint) {
		if (pb instanceof ProblemZ3|| pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3Incremental || 
				pb instanceof ProblemZ3BitVector || pb instanceof ProblemZ3BitVectorIncremental) {
			Object left = constraint.getLeft();
			Object right = constraint.getRight();
			if (left instanceof SelectExpression) {
				parseRAC_Select(((SelectExpression) left), constraint, ((RealExpression) right));
			} else if (left instanceof RealStoreExpression) {
				parseRAC_Store(((RealStoreExpression) left), constraint, ((ArrayExpression) right));
			} else {
				throw new RuntimeException("RealArrayConstraint is not select or store");
			}
			return true;
		} else {
			throw new RuntimeException("## Error : Real Array constraints only handled by z3. Try specifying a z3 instance as symbolic.dp");	
		}
	}

	//RealArrayConstraint Parsing Methods
	private void parseRAC_Select(SelectExpression selex, RealArrayConstraint rac, RealExpression sel_right) {
		assert selex != null;
		assert sel_right != null;

		ArrayExpression ae = selex.arrayExpression;
		Object selexRef = selex.indexExpression.accept(this);  //Visit the selex
		Object sel_rightRef = sel_right.accept(this);          //Visit the sel_right
		switch(rac.getComparator()) {
		case EQ:
			if(selexRef instanceof Long) {
				selexRef = pb.makeIntConst(((Long)selexRef).longValue());
			}

			if(sel_rightRef instanceof Double) {
				sel_rightRef = pb.makeRealConst(((Double)sel_rightRef).doubleValue());
			}

			pb.post(pb.eq(pb.realSelect(pb.makeRealArrayVar(ae.getName()), selexRef), sel_rightRef));
			break;
		case NE:
			pb.post(pb.neq(pb.select(pb.makeRealArrayVar(ae.getName()), selexRef), sel_rightRef));
			break;
		default:
			throw new RuntimeException("RealArrayConstraint - Unsupported comparator");
		}

	}

	private void parseRAC_Store(RealStoreExpression stoex, RealArrayConstraint rac, ArrayExpression sto_right) {
		assert stoex != null;
		assert sto_right != null;

		ArrayExpression ae = stoex.arrayExpression;
		ArrayExpression newae = sto_right;
		Object stoexRef = stoex.indexExpression.accept(this);  //Visit the stoex
		Object stoexValRef = stoex.value.accept(this);         //Visit the stoex value

		switch(rac.getComparator()) {
		case EQ:
			if(stoexRef instanceof Long) {
				stoexRef = pb.makeIntConst(((Long)stoexRef).longValue());
			}

			if(stoexValRef instanceof Double) {
				stoexValRef = pb.makeRealConst(((Double)stoexValRef).doubleValue());
			}

			pb.post(pb.eq(pb.realStore(pb.makeRealArrayVar(ae.getName()), stoexRef, stoexValRef), pb.makeArrayVar(newae.getName())));

			break;
		case NE:
			pb.post(pb.neq(pb.realStore(pb.makeRealArrayVar(ae.getName()), stoexRef, stoexValRef), newae));
			break;
		default:
			throw new RuntimeException("RealArrayConstraint - Unsupported comparator");
		}
	}
}
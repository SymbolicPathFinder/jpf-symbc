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

package gov.nasa.jpf.symbc.numeric;

import gov.nasa.jpf.symbc.concolic.FunctionExpression;
import gov.nasa.jpf.symbc.mixednumstrg.SpecialIntegerExpression;
import gov.nasa.jpf.symbc.mixednumstrg.SpecialRealExpression;
import gov.nasa.jpf.symbc.string.DerivedStringExpression;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringConstraint;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.symbc.string.SymbolicStringBuilder;

/**
 * A visitor for both constraints and expressions. Ideally, constraints should
 * be an extension of expressions themselves, but, alas!, they are not.
 * 
 * Each node N in the expression tree (which may be a DAG) has an operator, zero
 * or more operands O1, O2, O3, ..., and implements a routine called
 * "accept(ConstraintExpressionVisitor visitor)" which calls the methods of this
 * visitor in the following way:
 * 
 * <ol>
 * <li>When node N is encountered, visitor.preVisit(N).</li>
 * <li>Before the first operand O1 is visited, visitor.inVisitBefore(N, O1) is
 * called.</li>
 * <li>O1 is visited.</li>
 * <li>visitor.inVisitAfter(N, O1) is called.</li>
 * <li>Before the second operand O2 is visited, visitor.inVisitBefore(N, O2) is
 * called.</li>
 * <li>O2 is visited.</li>
 * <li>visitor.inVisitAfter(N, O2) is called.</li>
 * <li>...
 * <li>Before the operand Ok is visited, visitor.inVisitBefore(N, Ok) is called.
 * </li>
 * <li>Ok is visited.</li>
 * <li>visitor.inVisitAfter(N, Ok) is called.</li>
 * <li>Finally, once all the operands have been visited, visitor.postVisit(N) is
 * called.</li>
 * </ol>
 * 
 * For the moment, visitor.inVisitBefore(...) and visitor.inVisitAfter(...)
 * routines are not implemented. They would add another 1134 methods to this
 * class, and although it would not impact runtime efficiency, it does seem like
 * overkill.
 * 
 * @author Jaco Geldenhuys
 */
public abstract class ConstraintExpressionVisitor2 {

	/*--- CONSTRAINT VISITOR ROUTINES ---*/

	public void preVisit(Constraint constraint) {
	}

	public void preVisit(LinearIntegerConstraint constraint) {
	}

	public void preVisit(LogicalORLinearIntegerConstraints constraint) {
	}

	public void preVisit(MixedConstraint constraint) {
	}

	public void preVisit(NonLinearIntegerConstraint constraint) {
	}

	public void preVisit(RealConstraint constraint) {
	}

	public void postVisit(Constraint constraint) {
	}

	public void postVisit(LinearIntegerConstraint constraint) {
	}

	public void postVisit(LogicalORLinearIntegerConstraints constraint) {
	}

	public void postVisit(MixedConstraint constraint) {
	}

	public void postVisit(NonLinearIntegerConstraint constraint) {
	}

	public void postVisit(RealConstraint constraint) {
	}
	
	public void preVisit(StringConstraint stringConstraint) {		
	}
	
	public void postVisit(StringConstraint stringConstraint) {		
	}

	/*--- EXPRESSION VISITOR ROUTINES ---*/

	public void preVisit(Expression expr) {
	}

	public void preVisit(IntegerExpression expr) {
	}

	public void preVisit(LinearIntegerExpression expr) {
	}

	public void preVisit(BinaryLinearIntegerExpression expr) {
	}

	public void preVisit(IntegerConstant expr) {
	}

	public void preVisit(SymbolicInteger expr) {
	}

	public void preVisit(NonLinearIntegerExpression expr) {
	}

	public void preVisit(BinaryNonLinearIntegerExpression expr) {
	}

	public void preVisit(SpecialIntegerExpression expr) {
	}

	public void preVisit(RealExpression expr) {
	}

	public void preVisit(BinaryRealExpression expr) {
	}

	public void preVisit(FunctionExpression expr) {
	}

	public void preVisit(MathRealExpression expr) {
	}

	public void preVisit(RealConstant expr) {
	}

	public void preVisit(SpecialRealExpression expr) {
	}

	public void preVisit(SymbolicReal expr) {
	}

	public void preVisit(StringExpression expr) {
	}

	public void preVisit(DerivedStringExpression expr) {
	}

	public void preVisit(StringConstant expr) {
	}

	public void preVisit(StringSymbolic expr) {
	}

	public void preVisit(SymbolicStringBuilder expr) {
	}

	public void postVisit(Expression expr) {
	}

	public void postVisit(IntegerExpression expr) {
	}

	public void postVisit(LinearIntegerExpression expr) {
	}

	public void postVisit(BinaryLinearIntegerExpression expr) {
	}

//	public void postVisit(IntegerConstant expr) {
//	}

//	public void postVisit(SymbolicInteger expr) {
//	}

	public void postVisit(NonLinearIntegerExpression expr) {
	}

	public void postVisit(BinaryNonLinearIntegerExpression expr) {
	}

	public void postVisit(SpecialIntegerExpression expr) {
	}

	public void postVisit(RealExpression expr) {
	}

	public void postVisit(BinaryRealExpression expr) {
	}

	public void postVisit(FunctionExpression expr) {
	}



//	public void postVisit(RealConstant expr) {
//	}

	public void postVisit(SpecialRealExpression expr) {
	}

//	public void postVisit(SymbolicReal expr) {
//	}

	public void postVisit(StringExpression expr) {
	}

	public void postVisit(DerivedStringExpression expr) {
	}

	public void postVisit(StringConstant expr) {
	}

	public void postVisit(StringSymbolic expr) {
	}

	public void postVisit(SymbolicStringBuilder expr) {
	}

	
	//Added by Carson so far - First case visitors
	
	//These 4
	public boolean postVisit(Long left, LinearIntegerConstraint constraint, Long right) {
		return false;
	}
	
	public boolean postVisit(Long left, LinearIntegerConstraint constraint, Object right) {
		return false;
	}
	
	public boolean postVisit(Object left, LinearIntegerConstraint constraint, Long right) {
		return false;
	}
	
	public boolean postVisit(Object left, LinearIntegerConstraint constraint, Object right) {
		return false;
	}

	//These 4
	public boolean postVisit(Double left, RealConstraint constraint, Double right) {
		return false;
	}
	
	public boolean postVisit(Double left, RealConstraint constraint, Object right) {
		return false;
	}
	
	public boolean postVisit(Object left, RealConstraint constraint, Double right) {
		return false;
	}
	
	public boolean postVisit(Object left, RealConstraint constraint, Object right) {
		return false;
	}
	
	//These 4
	public Object postVisit(Long left, BinaryLinearIntegerExpression expression, Long right) {
		return null;
	}
	
	public Object postVisit(Long left, BinaryLinearIntegerExpression expression, Object right) {
		return null;
	}
	
	public Object postVisit(Object left, BinaryLinearIntegerExpression expression, Long right) {
		return null;
	}

	public Object postVisit(Object left, BinaryLinearIntegerExpression expression, Object right) {
		 return null;
	}
	
	//These 4
	public Object postVisit(Long left, BinaryNonLinearIntegerExpression expression, Long right) {
		return null;
	}
	
	public Object postVisit(Long left, BinaryNonLinearIntegerExpression expression, Object right) {
		return null;
	}
	
	public Object postVisit(Object left, BinaryNonLinearIntegerExpression expression, Long right) {
		return null;
	}

	public Object postVisit(Object left, BinaryNonLinearIntegerExpression expression, Object right) {
		return null;
	}
	
	//
	public Object postVisit(Double left, BinaryRealExpression expression, Double right) {
		return null;
	}
	
	public Object postVisit(Double left, BinaryRealExpression expression, Object right) {
		return null;
	}
	
	public Object postVisit(Object left, BinaryRealExpression expression, Double right) {
		return null;
	}

	public Object postVisit(Object left, BinaryRealExpression expression, Object right) {
		return null;
	}
	
	
	public Long postVisit(IntegerConstant expr) {
		return null;
	}
	
	public Object postVisit(SymbolicInteger expr) {
		return null;
	}
	
	public Double postVisit(RealConstant expr) {
		return null;
	}
	
	public Object postVisit(SymbolicReal expr) {
		return null;
	}
	
	public Object postVisit(Object leftExpr, MathRealExpression mathRealExpr, Object rightExpr) {
		return null;
	}


	//
	public boolean postVisit(Long left, NonLinearIntegerConstraint constraint, Long right) {
		return false;
	}
	
	public boolean postVisit(Object left, NonLinearIntegerConstraint constraint, Long right) {
		return false;
	}
	
	public boolean postVisit(Long left, NonLinearIntegerConstraint constraint, Object right) {
		return false;
	}
	
	public boolean postVisit(Object left, NonLinearIntegerConstraint constraint, Object right) {
		return false;
	}

	//
	public boolean postVisit(SymbolicReal left, MixedConstraint mixedConstraint, SymbolicInteger right) {
		return false;
	}

	public boolean postVisit(SymbolicReal left, MixedConstraint constraint, IntegerExpression right) {
		return false;
	}

	public boolean postVisit(RealExpression left, MixedConstraint constraint, SymbolicInteger right) {
		return false;
	}

	public boolean postVisit(RealExpression left, MixedConstraint constraint, IntegerExpression right) {
		return false;
	}

//	public boolean postVisit(Object l, Constraint constraint, Object r) {
//		// TODO Auto-generated method stub
//		return false;
//	}
}

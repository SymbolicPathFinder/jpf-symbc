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

import gov.nasa.jpf.symbc.arrays.ArrayConstraint;
import gov.nasa.jpf.symbc.arrays.RealArrayConstraint;

/**
 * An extension of the previous visitor system created for GREEN solver integration
 * set up for a more robust purpose of handling the functionality previously done by
 * PCParser. All it changes about the previous system is the creation of literal 
 * visit() methods that return values explicitly upon being called. The calling of 
 * accept() has been moved to these visit methods for simplicity purposes.
 * 
 * Not all methods have been moved over. As of now, only the methods needed to be moved
 * have been moved since many of the preVisit() and postVisit() methods visit constraints
 * or expressions that don't need visit() functionality to accomplish my initial goal.
 * 
 * @author Carson Smith
 */
public abstract class ConstraintExpressionVisitor2 extends ConstraintExpressionVisitor {

	/*--- CONSTRAINT VISITOR ROUTINES ---*/
	
	public boolean visit(Constraint constraint) {
		return false;
	}
	
	public boolean visit(LinearIntegerConstraint constraint) {
		return false;
	}
	
	public boolean visit(NonLinearIntegerConstraint constraint) {
		return false;
	}
	
	public boolean visit(RealConstraint constraint) {
		return false;
	}
	
	public boolean visit(MixedConstraint constraint) {
		return false;
	}
	
	public boolean visit(LogicalORLinearIntegerConstraints constraint) {
		return false;
	}
	
	public boolean visit(ArrayConstraint constraint) {
		return false;
	}
	
	public boolean visit(RealArrayConstraint constraint) {
		return false;
	}
	
	/*--- EXPRESSION VISITOR ROUTINES ---*/
	
	public Object visit(SymbolicInteger expr) {
		return null;
	}
	
	public Double visit(RealConstant expr) {
		return null;
	}
	
	public Object visit(SymbolicReal expr) {
		return null;
	}
	
	public Object visit(MathRealExpression expr) {
		return null;
	}
	
	public Object visit(BinaryLinearIntegerExpression expression) {
		return null;
	}

	public Object visit(BinaryNonLinearIntegerExpression expression) {
		return null;
	}

	public Object visit(BinaryRealExpression expression) {
		return null;
	}

	public Long visit(IntegerConstant integerConstant) {
		return null;
	}

}

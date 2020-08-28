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

import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.MixedConstraint;
import gov.nasa.jpf.symbc.numeric.RealConstant;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;

/**
 * A visitor used for parsing MixedConstraints to an instance of a solver, mimicking
 * the old functionality of PCParser.
 * 
 * @author Carson Smith
 */
public class MixedConstraintVisitor extends ProblemGeneralVisitor {

	/**
	 * CONSTRUCTOR: Creates a MixedConstraintVisitor object
	 * @param pb - The ProblemGeneral object you're initializing with.
	 */
	public MixedConstraintVisitor(ProblemGeneral pb) {
		super(pb);
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
	private boolean parseMC_OO(RealExpression left, MixedConstraint constraint, IntegerExpression right) {
		//However, instead of a false assert, it'd probably be better to throw a Runtime Exception of some sort.
		assert(false); //This should be unreachable according to the code's author.
		return true;
	}

	private boolean parseMC_OI(RealExpression left, MixedConstraint constraint, SymbolicInteger right) {
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

	private boolean parseMC_RO(SymbolicReal left, MixedConstraint constraint, IntegerExpression right) {
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
	
}

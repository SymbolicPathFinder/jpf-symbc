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

import gov.nasa.jpf.symbc.numeric.RealConstraint;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;

/**
 * A visitor used for parsing RealConstraints to an instance of a solver, mimicking
 * the old functionality of PCParser.
 * 
 * @author Carson Smith
 */
public class RealConstraintVisitor extends ProblemGeneralVisitor {

	/**
	 * CONSTRUCTOR: Creates a RealConstraintVisitor object
	 * @param pb - The ProblemGeneral object you're initializing with.
	 */
	public RealConstraintVisitor(ProblemGeneral pb) {
		super(pb);
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
	private boolean parseRC_OO(Object left, RealConstraint constraint, Object right) {
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

	private boolean parseRC_OD(Object left, RealConstraint constraint, Double right) {
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

	private boolean parseRC_DO(Double left, RealConstraint constraint, Object right) {
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

	private boolean parseRC_DD(Double left, RealConstraint constraint, Double right) {
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
}

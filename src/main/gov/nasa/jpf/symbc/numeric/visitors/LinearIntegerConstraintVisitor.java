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

import java.util.Map;

import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;

/**
 * This class represents a visitor for LinearIntegerConstraints. The expected functionality is that
 * 
 * @author Carson Smith
 */
public class LinearIntegerConstraintVisitor extends ProblemGeneralVisitor {

	public LinearIntegerConstraintVisitor(ProblemGeneral pb) {
		super(pb);
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
}
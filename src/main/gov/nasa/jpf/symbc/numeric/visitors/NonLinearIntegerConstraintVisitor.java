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

import gov.nasa.jpf.symbc.numeric.NonLinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemCoral;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVector;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVectorIncremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Incremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Optimize;

public class NonLinearIntegerConstraintVisitor extends ProblemGeneralVisitor {

	public NonLinearIntegerConstraintVisitor(ProblemGeneral pb) {
		super(pb);
	}
	
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
}

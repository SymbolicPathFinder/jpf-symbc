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

import gov.nasa.jpf.symbc.arrays.ArrayExpression;
import gov.nasa.jpf.symbc.arrays.RealArrayConstraint;
import gov.nasa.jpf.symbc.arrays.RealStoreExpression;
import gov.nasa.jpf.symbc.arrays.SelectExpression;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVector;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVectorIncremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Incremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Optimize;

public class RealArrayConstraintVisitor extends ProblemGeneralVisitor {

	public RealArrayConstraintVisitor(ProblemGeneral pb) {
		super(pb);
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

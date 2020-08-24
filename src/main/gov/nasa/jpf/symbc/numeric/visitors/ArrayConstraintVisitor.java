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

import gov.nasa.jpf.symbc.arrays.ArrayConstraint;
import gov.nasa.jpf.symbc.arrays.ArrayExpression;
import gov.nasa.jpf.symbc.arrays.InitExpression;
import gov.nasa.jpf.symbc.arrays.SelectExpression;
import gov.nasa.jpf.symbc.arrays.StoreExpression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVector;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVectorIncremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Incremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Optimize;

/**
 * Used for parsing out ArrayConstraints to a solver.
 * 
 * @author Carson Smith 
 */
public class ArrayConstraintVisitor extends ProblemGeneralVisitor {

	public ArrayConstraintVisitor(ProblemGeneral pb) {
		super(pb);
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
	
}

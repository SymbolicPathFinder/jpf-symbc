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
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.RealConstant;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVector;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3BitVectorIncremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Incremental;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemZ3Optimize;

/**
 * Used for parsing out RealArrayConstraints to a solver.
 * 
 * In the near future, I'll get around to refactoring this class to follow the
 * visitor system more closely, probably with unique ways of parsing the types of
 * ArrayExpressions.
 * 
 * @author Carson Smith 
 */
public class RealArrayConstraintVisitor extends ProblemGeneralVisitor {

	public RealArrayConstraintVisitor(ProblemGeneral pb) {
		super(pb);
	}

	//RealArrayConstraint Visitor
	@Override
	public boolean visit(RealArrayConstraint constraint) {
		//TODO: Get rid of this instance of statement for pb types that can solve Array-based constraints.
		if (pb instanceof ProblemZ3|| pb instanceof ProblemZ3Optimize || pb instanceof ProblemZ3Incremental || 
				pb instanceof ProblemZ3BitVector || pb instanceof ProblemZ3BitVectorIncremental) {
			
			final Comparator c_compRef = constraint.getComparator();


	        SelectExpression selex = null;
	        RealStoreExpression stoex = null;
	        RealExpression sel_right = null;
	        ArrayExpression sto_right = null;
	        if (constraint.getLeft() instanceof SelectExpression) {
	             selex = (SelectExpression)constraint.getLeft();
	             sel_right = (RealExpression)constraint.getRight();
	        } else if (constraint.getLeft() instanceof RealStoreExpression) {
	           stoex = (RealStoreExpression)constraint.getLeft();
	           sto_right = (ArrayExpression)constraint.getRight();
	        } else {
	           throw new RuntimeException("ArrayConstraint is not select or store");
	        }

	        switch(c_compRef) {
	        case EQ:

	            if (selex != null && sel_right != null) {
	                // The array constraint is a select
	                ArrayExpression ae = selex.arrayExpression;
	                pb.post(pb.eq(pb.realSelect(pb.makeRealArrayVar(ae.getName()),
	                  (selex.indexExpression instanceof IntegerConstant) ? pb.makeIntConst(((IntegerConstant)selex.indexExpression).value) :
	selex.indexExpression.accept(this)),
	                  (sel_right instanceof RealConstant) ? pb.makeRealConst(((RealConstant)sel_right).value) :
	sel_right.accept(this)));
	                break;
	            }
	            if (stoex != null && sto_right != null) {
	                // The array constraint is a store
	                ArrayExpression ae = stoex.arrayExpression;
	                ArrayExpression newae = sto_right;
	                pb.post(pb.eq(pb.realStore(pb.makeRealArrayVar(ae.getName()),
	                  (stoex.indexExpression instanceof IntegerConstant) ? pb.makeIntConst(((IntegerConstant)stoex.indexExpression).value) :
	stoex.indexExpression.accept(this),
	                  (stoex.value instanceof RealConstant) ? pb.makeRealConst(((RealConstant)stoex.value).value) :
	stoex.value.accept(this)),
	                   pb.makeRealArrayVar(newae.getName())));
	                break;
	            }
	            throw new RuntimeException("ArrayConstraint is not correct select or store");
	        case NE:
	            if (selex != null && sel_right != null) {
	                // The array constraint is a select
	                ArrayExpression ae = selex.arrayExpression;
	                pb.post(pb.neq(pb.realSelect(pb.makeRealArrayVar(ae.getName()), selex.indexExpression.accept(this)),
	sel_right.accept(this)));
	                break;
	            }
	            if (stoex != null && sto_right != null) {
	                // The array constraint is a store
	                ArrayExpression ae = stoex.arrayExpression;
	                ArrayExpression newae = sto_right;
	                pb.post(pb.neq(pb.realStore(pb.makeRealArrayVar(ae.getName()), stoex.indexExpression.accept(this),
	stoex.value.accept(this)), newae));
	                break;
	            }
	            throw new RuntimeException("ArrayConstraint is not correct select or store");
	        default:
	            throw new RuntimeException("ArrayConstraint is not select or store");
	        }
	        return true;
		} else {
			throw new RuntimeException("## Error : Real Array constraints only handled by z3. Try specifying a z3 instance as symbolic.dp");	
		}
	}
}

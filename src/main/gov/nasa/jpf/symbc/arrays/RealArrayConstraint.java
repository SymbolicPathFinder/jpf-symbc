/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * The Java Pathfinder core (jpf-core) platform is licensed under the
 * Apache License, Version 2.0 (the "License"); you may not use this file except
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

// author Aymeric Fromherz aymeric.fromherz@ens.fr
package gov.nasa.jpf.symbc.arrays;

import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor2;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.RealExpression;

public class RealArrayConstraint extends Constraint {
    public RealArrayConstraint(SelectExpression se, Comparator c, RealExpression ae) {
        super(se, c, ae);
    }

    public RealArrayConstraint(RealStoreExpression se, Comparator c, ArrayExpression ae) {
        super(se, c, ae);
    }

    public Constraint copy() {
        if (getLeft() instanceof SelectExpression) {
            return new RealArrayConstraint((SelectExpression)getLeft(), getComparator(), (RealExpression)getRight());
        } else {
            return new RealArrayConstraint((RealStoreExpression)getLeft(), getComparator(), (ArrayExpression)getRight());
        }
    }

    public RealArrayConstraint not() {
        try {
            return new RealArrayConstraint((SelectExpression)super.getLeft(), getComparator().not(), (RealExpression)getRight());
        } catch (Exception e) {
            try {
                return new RealArrayConstraint((RealStoreExpression)super.getLeft(), getComparator().not(), (ArrayExpression)getRight());
            } catch (Exception r) {
                throw new RuntimeException("ArrayConstraint is not select or store");
            }
        }
    }
    
    //Carson Smith
    public boolean accept(ConstraintExpressionVisitor2 visitor) {
		visitor.preVisit(this);
		boolean result = visitor.visit(this);
		visitor.postVisit(this);
		return result;
	}
}


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
//
package gov.nasa.jpf.symbc.arrays;

import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;

public class ArrayConstraint extends Constraint {
    public ArrayConstraint(SelectExpression se, Comparator c, IntegerExpression ae) {
        super(se, c, ae);
    }

    public ArrayConstraint(StoreExpression se, Comparator c, ArrayExpression ae) {
        super(se, c, ae);
    }

    public ArrayConstraint(InitExpression ie, Comparator c, ArrayExpression ae) {
      super(ie, c, ae);
    }

    public Constraint copy() {
        if (this.getLeft() instanceof SelectExpression) {
            return new ArrayConstraint((SelectExpression)getLeft(), getComparator(), (IntegerExpression)getRight());
        } else if (this.getLeft() instanceof StoreExpression) {
            return new ArrayConstraint((StoreExpression)getLeft(), getComparator(), (ArrayExpression)getRight());
        } else {
            return new ArrayConstraint((InitExpression)getLeft(), getComparator(), (ArrayExpression)getRight());
        }
    }

    public ArrayConstraint not() {
        try {
            return new ArrayConstraint((SelectExpression)super.getLeft(), getComparator().not(), (IntegerExpression)getRight());
        } catch (Exception e) {
            try {
                return new ArrayConstraint((StoreExpression)super.getLeft(), getComparator().not(), (ArrayExpression)getRight());
            } catch (Exception r) {
                throw new RuntimeException("Negation of an arrayConstraint that is not select or store");
            }
        }
    }
}


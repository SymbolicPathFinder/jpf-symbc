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

import gov.nasa.jpf.symbc.numeric.ConstraintExpressionVisitor;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;

import java.util.Map;

public class SelectExpression extends Expression {
    public ArrayExpression arrayExpression;
    public IntegerExpression indexExpression;

    public SelectExpression(ArrayExpression ae, IntegerExpression ie) {
        this.arrayExpression = ae;
        this.indexExpression = ie;
    }

    public void accept(ConstraintExpressionVisitor visitor) {
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    public void getVarsVals(Map<String, Object> varsVals) {
        return;
    }

    public String stringPC() {
        return arrayExpression.stringPC() + "[" + indexExpression.stringPC() + "]";
    }

    public int compareTo(Expression expr) {
        // unimplemented
        return 0;
    }

    public String toString() {
        return this.stringPC();
    }
}

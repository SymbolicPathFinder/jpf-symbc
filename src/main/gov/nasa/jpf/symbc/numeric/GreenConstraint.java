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

package gov.nasa.jpf.symbc.numeric;

import za.ac.sun.cs.green.expr.Expression;
public class GreenConstraint extends Constraint {

	private Expression exp;

	public GreenConstraint() {
		super(null, null, null);
		exp = null;
	}

	public GreenConstraint(Expression e) {
		super(null, null, null);
		exp = e;
	}

	public Expression getExp() {
		return exp;
	}

	public Constraint copy() {
		return new GreenConstraint(exp);
	}


		@Override
	public Constraint not() { // TODO: look closer to that later on
		throw new UnsupportedOperationException("Not supported");
		//return null;
	}

	public String toString() {
		return (exp.toString());	}

	public String stringPC() {
		return this.toString();
	}

	public boolean equals(Object o) {
		if (!(o instanceof GreenConstraint))
			return false;
		return (exp.equals(((GreenConstraint) o).exp));
	}

}
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

import java.util.ArrayList;
import java.util.List;

public class LogicalORLinearIntegerConstraints extends Constraint{
	
	private List<LinearIntegerConstraint> list;
	public String comment;
	
	public LogicalORLinearIntegerConstraints () {
		super (null, null, null);
		list = new ArrayList<LinearIntegerConstraint>();
	}
	
	public LogicalORLinearIntegerConstraints (List<LinearIntegerConstraint> l) {
		super (null, null, null);
		list = l;
	}
	
	
	public void addToList (LinearIntegerConstraint lic) {
		if (!list.contains(lic)) {
			list.add(lic);
		}
	}

	public List<LinearIntegerConstraint> getList () {
		return list;
	}
	
	@Override
	public Constraint not() {
		throw new UnsupportedOperationException("Not supported");
		//return null;
	}
	
	public String toString () {
		StringBuilder sb = new StringBuilder();
		if (list.size() == 1) {
			return list.get(0).toString();
		}
		else {
			sb.append (list.get(0).toString());
		}
		for (int i = 1; i < list.size(); i++) {
			sb.append (" OR ");
			sb.append (list.get(i).toString());
		}
		sb.append ("(" + comment + ")");
		if (and != null) {
			sb.append (" && \n");
			sb.append (and.stringPC());
		}
		return sb.toString();
	}
	
	public String stringPC () {
		return this.toString();
	}
	
	public boolean equals (Object o) {
		if (!(o instanceof LogicalORLinearIntegerConstraints))
			return false;
		LogicalORLinearIntegerConstraints other = (LogicalORLinearIntegerConstraints) o;
		if (this.list.size() != other.list.size()) {
			return false;
		}
		for (int i = 0; i < this.list.size(); i++) {
			if (!this.list.get(i).equals(other.list.get(i))) {
				return false;
			}
		}
		return true;
	}
	
	public boolean accept(ConstraintExpressionVisitor2 visitor) {
		visitor.preVisit(this);
		boolean result = visitor.visit(this);
		visitor.postVisit(this);
		return result;
	}
}

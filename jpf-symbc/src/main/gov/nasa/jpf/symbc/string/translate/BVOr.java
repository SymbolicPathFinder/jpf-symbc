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

package gov.nasa.jpf.symbc.string.translate;

public class BVOr implements BVExpr{
	public BVExpr left, right;
	
	public BVOr (BVExpr left, BVExpr right) {
		this.left = left;
		this.right = right;
	}

	public String toString () {
		StringBuffer sb = new StringBuffer ();
		sb.append ("(");
		sb.append (left.toString());
		sb.append (") OR (");
		sb.append (right.toString());
		sb.append (")");
		return sb.toString();
	}
		
	public String toSMTLib () {
		StringBuffer sb = new StringBuffer ();
		sb.append("(or ");
		sb.append (left.toSMTLib());
		sb.append (" ");
		sb.append (right.toSMTLib());
		sb.append (")");
		return sb.toString();
	}
	
	
}

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

public class BVNot implements BVExpr{
	public BVExpr expr;
	
	public BVNot (BVExpr expr) {
		this.expr = expr;
	}
	
	public String toString () {
		StringBuffer sb = new StringBuffer ();
		
		sb.append ("not (");
		sb.append (expr.toString());
		sb.append (")");
		
		return sb.toString();
	}
	
	public String toSMTLib () {
		StringBuffer sb = new StringBuffer ();
		
		sb.append("(not ");
		sb.append(expr.toSMTLib());
		sb.append(")");
		
		return sb.toString();
	}
}

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

//
// Copyright (C) 2007 United States Government as represented by the
// Administrator of the National Aeronautics and Space Administration
// (NASA).  All Rights Reserved.
//
// This software is distributed under the NASA Open Source Agreement
// (NOSA), version 1.3.  The NOSA has been approved by the Open Source
// Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
// directory tree for the complete NOSA document.
//
// THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
// KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
// LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
// SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
// THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
// DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//
package gov.nasa.jpf.symbc.numeric;

import java.util.Map;
import java.util.StringTokenizer;

public class PreCondition {
	PathCondition pc;


	public PathCondition createPathCondition(String assumeString,
			Map<String,Expression> expressionMap) {

		//System.out.println("Pre-condition: "+assumeString);
		pc = new PathCondition();
		if (assumeString.contains("&&")){
			StringTokenizer st = new StringTokenizer(assumeString,"&&");
			while (st.hasMoreTokens()){
				String expressionString = st.nextToken();
				addExpression(expressionString,expressionMap);
			}
		}else{
			addExpression(assumeString,expressionMap);
		}
		return pc;
	}

	public PathCondition addConstraints(PathCondition pc, String assumeString,
			Map<String,Expression> expressionMap) {

		this.pc = pc;
		if (assumeString.contains("&&")){
			StringTokenizer st = new StringTokenizer(assumeString,"&&");
			while (st.hasMoreTokens()){
				String expressionString = st.nextToken();
				addExpression(expressionString,expressionMap);
			}
		}else{
			addExpression(assumeString,expressionMap);
		}

		return pc;
	}

	/*
	 * Helper method to parse expression string to add to pc
	 */
	// needs to be extended for more complex expressions
	// TODO: check
	private void addExpression(String expressionString,
			Map<String,Expression> expressionMap){

		StringTokenizer st = null;
		//String operator = "";
		Comparator c;
		String lhs = "";
		String rhs = "";
		Expression lhsExpression = null;
		Expression rhsExpression = null;
		long lhsInt, rhsInt;
		double lhsDouble, rhsDouble;

		if (expressionString.contains("!=")){
			st = new StringTokenizer(expressionString,"!=");
			c= Comparator.NE;
			lhs = st.nextToken();
			rhs = st.nextToken();
		}else if (expressionString.contains("==")){
			st = new StringTokenizer(expressionString,"==");
			c = Comparator.EQ;
			lhs = st.nextToken();
			rhs = st.nextToken();
		}else if (expressionString.contains(">=")){
			st = new StringTokenizer(expressionString,">=");
			c = Comparator.GE;
			lhs = st.nextToken();
			rhs = st.nextToken();
		}else if (expressionString.contains("<=")){
			st = new StringTokenizer(expressionString,"<=");
			c = Comparator.LE;
			lhs = st.nextToken();
			rhs = st.nextToken();
		}else if (expressionString.contains(">")){
			st = new StringTokenizer(expressionString,">");
			c = Comparator.GT;
			lhs = st.nextToken();
			rhs = st.nextToken();

		}else if (expressionString.contains("<")){
			st = new StringTokenizer(expressionString,"<");
			c = Comparator.LT;
			lhs = st.nextToken();
			rhs = st.nextToken();
		}else
			throw new RuntimeException("## Error: parse error in pre-condition (op)");



		if (expressionMap.containsKey(lhs))
			lhsExpression = expressionMap.get(lhs);
		else {
			// expect a number here
			try{
				lhsInt = Long.parseLong(lhs);
				lhsExpression = new IntegerConstant(lhsInt);
			}
			catch(Exception e1){
				try {
					lhsDouble = Double.parseDouble(lhs);
					lhsExpression = new RealConstant(lhsDouble);
				}
				catch(Exception e2) {
					throw new RuntimeException("## Error: parse error in pre-condition " + lhs + "not a number");
				}
			}
		}


		if (expressionMap.containsKey(rhs))
			rhsExpression = expressionMap.get(rhs);
		else {
			//expect a number here
			try{
				rhsInt = Long.parseLong(rhs);
				rhsExpression = new IntegerConstant(rhsInt);
			}
			catch(Exception e1){
				try {
					rhsDouble = Double.parseDouble(rhs);
					rhsExpression = new RealConstant(rhsDouble);
				}
				catch(Exception e2) {
					throw new RuntimeException("## Error: parse error in pre-condition " + rhs + "not a number");
				}
			}
		}

		pc._addDet(c, lhsExpression, rhsExpression);
	}
}

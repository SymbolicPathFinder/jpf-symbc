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

package gov.nasa.jpf.symbc.concolic;

import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.RealConstant;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;
import java.util.StringTokenizer;

public class Partition {
	

	public static ArrayList<PathCondition> createConditions(String[] partitions,
			Map<String,Expression> expressionMap) {
		if(partitions == null) return null;
		ArrayList<PathCondition> conditions
		 	= new ArrayList<PathCondition>();
		for(int partIndex = 0; partIndex < 
						partitions.length; partIndex++) {
			PathCondition cond = createPathCondition(partitions[partIndex],
					expressionMap);
			conditions.add(cond);
		}
		return conditions;
	}
	
	public static PathCondition createPathCondition(String assumeString,
			Map<String,Expression> expressionMap) {

		//System.out.println("Pre-condition: "+assumeString);
		PathCondition pc = new PathCondition();
		if (assumeString.contains("&&")){
			StringTokenizer st = new StringTokenizer(assumeString,"&&");
			while (st.hasMoreTokens()){
				String expressionString = st.nextToken();
				addExpression(expressionString,expressionMap, pc);
			}
		}else{
			addExpression(assumeString,expressionMap, pc);
		}

		//System.out.println("parition "+pc);
		return pc;
	}

	public PathCondition addConstraints(PathCondition pc, String assumeString,
			Map<String,Expression> expressionMap) {

		//System.out.println("Precondition: "+assumeString);

		if (assumeString.contains("&&")){
			StringTokenizer st = new StringTokenizer(assumeString,"&&");
			while (st.hasMoreTokens()){
				String expressionString = st.nextToken();
				addExpression(expressionString,expressionMap, pc);
			}
		}else{
			addExpression(assumeString,expressionMap, pc);
		}

		//System.out.println("added precondition "+ assumeString);
		//System.out.println("PC: "+ pc);
		return pc;
	}

	/*
	 * Helper method to parse expression string to add to pc
	 */
	// needs to be extended for more complex expressions
	// TODO: check
	private static void addExpression(String expressionString,
			Map<String,Expression> expressionMap, PathCondition pc){

		StringTokenizer st = null;
		//String operator = "";
		Comparator c;
		String lhs = "";
		String rhs = "";
		Expression lhsExpression = null;
		Expression rhsExpression = null;
		int lhsInt, rhsInt;
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

		//System.out.println("expressionMap :" + expressionMap.toString());
		//System.out.println("lhs.toString :" + lhs.toString());

		//Iterator<String> expMap = expressionMap.keySet().iterator();
		//while(expMap.hasNext()) {
		//	System.out.println(expMap.next());
			
		//}
		
		if (expressionMap.containsKey(lhs)) {
			lhsExpression = expressionMap.get(lhs.toString());
		}
		else {
			// expect a number here
			try{
				lhsInt = Integer.parseInt(lhs);
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
				rhsInt = Integer.parseInt(rhs);
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
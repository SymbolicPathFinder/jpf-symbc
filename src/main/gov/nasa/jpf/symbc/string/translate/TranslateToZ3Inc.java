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

import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringUtility;
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;
import gov.nasa.jpf.symbc.string.graph.Edge;
import gov.nasa.jpf.symbc.string.graph.EdgeCharAt;
import gov.nasa.jpf.symbc.string.graph.EdgeConcat;
import gov.nasa.jpf.symbc.string.graph.EdgeContains;
import gov.nasa.jpf.symbc.string.graph.EdgeEndsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeEqual;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOf;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOf2;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOfChar;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOfChar2;
import gov.nasa.jpf.symbc.string.graph.EdgeLastIndexOf;
import gov.nasa.jpf.symbc.string.graph.EdgeLastIndexOfChar;
import gov.nasa.jpf.symbc.string.graph.EdgeLastIndexOfChar2;
import gov.nasa.jpf.symbc.string.graph.EdgeNotCharAt;
import gov.nasa.jpf.symbc.string.graph.EdgeNotContains;
import gov.nasa.jpf.symbc.string.graph.EdgeNotEndsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeNotEqual;
import gov.nasa.jpf.symbc.string.graph.EdgeNotStartsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeStartsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeSubstring1Equal;
import gov.nasa.jpf.symbc.string.graph.EdgeSubstring2Equal;
import gov.nasa.jpf.symbc.string.graph.EdgeTrimEqual;
import gov.nasa.jpf.symbc.string.graph.StringGraph;
import gov.nasa.jpf.symbc.string.graph.Vertex;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.Map.Entry;

import javax.management.RuntimeErrorException;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

public class TranslateToZ3Inc {
	
	protected static BVExpr expr;
	/* This number can be calculated beforehand */
	private static final int MAXVAR = 100000;
	/* Size of string */
	private static final int MAX_SIZE_OF_STRINGS = 100;
	
	private static Map<Vertex, BVExpr> map;
	private static int vectorOffset;
	
	private static int varIndex;
	
	//public static int totalTiming = 0;
	
	private static boolean printClauses = true;
	private static boolean logging = true;
	
	private static StringGraph global_graph;
	private static PathCondition global_pc;
	
	private static boolean Z3EverCalled;
	
	private static SymbolicConstraintsGeneral scg;
	
	private static Z3Interface z3Interface;
	
	public static long duration = 0;
	public static long int_duration = 0;
	public static long loops = 0;
	
	/*stack to keep track of what happened*/
	static Stack<LogicalORLinearIntegerConstraints> stack1;
	static Stack<LinearIntegerConstraint> stack2;
	
	public static boolean isSat (StringGraph g, PathCondition pc) {
		stack1 = new Stack<LogicalORLinearIntegerConstraints>();
		stack2 = new Stack<LinearIntegerConstraint>();
		long startTime = System.currentTimeMillis();
		boolean result = inner_isSat(g, pc);
		duration = duration + (System.currentTimeMillis() - startTime);
		if (result == false) {
			//println ("Stack: [" + stack1.toString() + "]");
		}
		return result;
	}
	
	//most sign, first letter
	private static boolean inner_isSat (StringGraph g, PathCondition pc) {
		loops++;
		SymbolicStringConstraintsGeneral.checkTimeOut();
		if (scg == null) scg = new SymbolicConstraintsGeneral();
		Z3EverCalled = false;
		global_graph = g;
		global_pc = pc;
		expr = null;
		//println ("[isSat] Bitvector: PC passed on: " + pc.header);
		//println ("Entered Z3");
		map = new HashMap<Vertex, BVExpr>();
		
		if (z3Interface == null) {
			try {
				z3Interface = new Z3Interface();
			} catch (Exception e) {
				e.printStackTrace();
				throw new RuntimeException("Could not load up z3\nMake sure the Z3 binary is in lib directory");
			}
		}
		
		//println ("[isSat] Walking through the edges");
		for (Edge e: g.getEdges()) {
			//println ("Edge: " + e);
			boolean result = handle(e);
			if (result == false) {
				//Add new constraints
				LogicalORLinearIntegerConstraints resultloic = new LogicalORLinearIntegerConstraints();
				for (LogicalORLinearIntegerConstraints temploic: stack1) {
					for (LinearIntegerConstraint lic: temploic.getList()) {
						if (lic.getComparator() == Comparator.NE) {
							LinearIntegerConstraint reverse = new LinearIntegerConstraint(lic.getRight(), Comparator.EQ, lic.getLeft());
							LinearIntegerConstraint tempLic = new LinearIntegerConstraint(lic.getLeft(), Comparator.EQ, lic.getRight());
							if (!(pc.hasConstraint(tempLic) || pc.hasConstraint(reverse))) {
								resultloic.addToList(lic);
							}
							else {
								//println ("Not adding 2: " + lic);
							}
						}
						else {
							resultloic.addToList(lic);
						}
					}
				}
				for (LinearIntegerConstraint lic: stack2) {
					if (lic.getComparator() == Comparator.NE) {
						LinearIntegerConstraint reverse = new LinearIntegerConstraint(lic.getRight(), Comparator.EQ, lic.getLeft());
						LinearIntegerConstraint tempLic = new LinearIntegerConstraint(lic.getLeft(), Comparator.EQ, lic.getRight());
						if (!(pc.hasConstraint(tempLic) || pc.hasConstraint(reverse))) {
							resultloic.addToList(lic);
						}
						else {
							//println ("Not adding 2: " + lic);
						}
					}
					else {
						resultloic.addToList(lic);
					}
				}
				resultloic.comment = "Removing path";
				//println ("Adding: " + resultloic);
				pc._addDet(resultloic);
				
				if (PathCondition.flagSolved == false) {
					//println ("[isSat] Path Condition changed, starting integer solver...");
					long startTime = System.currentTimeMillis();
					boolean int_result = scg.isSatisfiable(pc);
					long temp_dur = (System.currentTimeMillis() - startTime);
					int_duration = int_duration + temp_dur;
					duration -= temp_dur;
					if (int_result) {
						//println ("[isSat] Found to be sat, solving...");
						scg.solve(pc);
						PathCondition.flagSolved = true;
						//println ("[isSat] solved " + global_pc.header.toString());
						z3Interface.close(); z3Interface = null;
						stack1 = new Stack<LogicalORLinearIntegerConstraints>();
						stack2 = new Stack<LinearIntegerConstraint>();
						
						return inner_isSat (g, pc); //remove recursion
					}
					else {
						//println ("[isSat] integer solver could not solve");
						//println ("[isSat] string expr: " + expr.toString());
						//println ("[isSat] not solved: " + global_pc.header.toString());
						z3Interface.close(); z3Interface = null;
						return false;
					}
				}
				else {
					//println ("No change to path condition");
					z3Interface.close(); z3Interface = null;
					return false;
				}
			}
		}
		//println ("Done with edges");
		if (!Z3EverCalled) {
			z3Interface.close(); z3Interface = null;
			return true;
		}
		
		//println ("[post] Formula to check: " + vc.trueExpr());
		//println ("[post] On top of       : " + vc.getAssumptions());
		if (z3Interface.isSAT()) {
			//println ("Z3 interface SAT");
			Map<String, String> ans = z3Interface.getAns();
			
        	//println(model.toString());
        	
        	for (Entry<String, String> entry: ans.entrySet()) {
        		String vertexName = BVVar.reverseMap.get(entry.getKey().charAt(0));
        		String rawData = entry.getValue();
        		
        		rawData = fromRawData(rawData);
        		
        		////println (vertexName + " = " + rawData);
        		Vertex v = g.findVertex(vertexName);
        		v.setSolution(rawData);
        	}
           // System.out.//println("Satisfiable (Invalid)\n");
        	z3Interface.close(); z3Interface = null;
        	//println ("Returning true");
            return true;
		}
		else {
			//println ("Z3 interface UNSAT");
			z3Interface.close(); z3Interface = null;
			return false;
		}
	}
	
	//TODO add EdgeLastIndexOf
	private static boolean handle (Edge e) {
		if (e instanceof EdgeStartsWith) {
			return handleEdgeStartsWith ((EdgeStartsWith) e);
		}
		else if (e instanceof EdgeNotStartsWith) {
			return handleEdgeNotStartsWith((EdgeNotStartsWith) e);
		}
		else if (e instanceof EdgeEndsWith) {
			return handleEdgeEndsWith ((EdgeEndsWith) e);
		}
		else if (e instanceof EdgeNotEndsWith) {
			return handleEdgeNotEndsWith((EdgeNotEndsWith) e);
		}
		else if (e instanceof EdgeNotEqual) {
			return handleEdgeNotEqual((EdgeNotEqual) e);
		}
		else if (e instanceof EdgeTrimEqual) {
			return handleEdgeTrim((EdgeTrimEqual) e);
		}
		else if (e instanceof EdgeSubstring1Equal) {
			return handleEdgeSubstring1Equal((EdgeSubstring1Equal) e);
		}
		else if (e instanceof EdgeSubstring2Equal) {
			return handleEdgeSubstring2Equal((EdgeSubstring2Equal) e);
		}
		else if (e instanceof EdgeConcat) {
			return handleEdgeConcat((EdgeConcat) e);
		}
		else if (e instanceof EdgeCharAt) {
			return handleEdgeCharAt((EdgeCharAt) e);
		}
		else if (e instanceof EdgeNotCharAt) {
			return handleEdgeNotCharAt((EdgeNotCharAt) e);
		}
		else if (e instanceof EdgeIndexOf) {
			return handleEdgeIndexOf((EdgeIndexOf) e);
		}
		else if (e instanceof EdgeIndexOf2) {
			return handleEdgeIndexOf2((EdgeIndexOf2) e);
		}
		else if (e instanceof EdgeIndexOfChar) {
			return handleEdgeIndexOfChar((EdgeIndexOfChar) e);
		}
		else if (e instanceof EdgeIndexOfChar2) {
			return handleEdgeIndexOfChar2((EdgeIndexOfChar2) e);
		}
		else if (e instanceof EdgeContains) {
			return handleEdgeContains((EdgeContains) e);
		}
		else if (e instanceof EdgeNotContains) {
			return handleEdgeNotContains((EdgeNotContains) e);
		}
		else if (e instanceof EdgeLastIndexOfChar) {
			return handleEdgeLastIndexOfChar((EdgeLastIndexOfChar) e);
		}
		else if (e instanceof EdgeLastIndexOfChar2) {
			return handleEdgeLastIndexOfChar2((EdgeLastIndexOfChar2) e);
		}
		else {
			throw new RuntimeException("Not handled: " + e.getClass());
		}
	}
	
	private static String fromRawData (String data) {
		StringBuilder result = new StringBuilder ();
		StringBuilder word = new StringBuilder();
		int count = 0;
		//Skip "0bin"
		for (int i = 0; i < data.length(); i++) {
			if (count == 8) {
				result.append((char) Integer.parseInt(word.toString(), 2));
				word = new StringBuilder();
				count = 0;
			}
			word.append(data.charAt(i));
			count++;
		}
		result.append((char) Integer.parseInt(word.toString(), 2));
		return result.toString();
	}
	
	private static boolean handleEdgeStartsWith (EdgeStartsWith e) {
		//println ("[handleEdgeStartsWith] entered: " + e.toString());
		boolean result = false;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			//println ("startswith branch 1");
			BVExpr source = getBVExpr (e.getSource());
			BVExpr dest = getBVExpr (e.getDest());
			BVExpr temp = new BVExtract(source, e.getSource().getLength() * 8 - 1, (e.getSource().getLength() - e.getDest().getLength() + 1) * 8 - 8);
			result = post(new BVEq (temp, dest));
		}
		else if (!e.getSource().isConstant()) {
			//println ("startswith branch 2");
			BVExpr source = getBVExpr(e.getSource());
			String constant = e.getDest().getSolution();
			//println ("[startsWith] constant: " + constant);
			BVExpr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				BVExpr temp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
				char character = constant.charAt(i);
				if (lit == null) {
					lit = new BVEq(temp, new BVConst(character));
				}
				else {
					lit = new BVAnd(lit, new BVEq(temp, new BVConst(character)));
				}
			}
			//println ("[startsWith] Adding lit: " + lit);
			boolean temp_result = post (lit);
			//println ("[startsWith] returning: " + temp_result);
			result = temp_result;
		}
		else if (!e.getDest().isConstant()) {
			//println ("startswith branch 3");
			//TODO: Fix
			BVExpr dest = getBVExpr(e.getDest());
			String constant = e.getSource().getSolution();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
				char character = constant.charAt(i);
				lit = and(lit, new BVEq (temp, new BVConst(character)));
			}
			/*for (int j = 0; j < constant.length(); j++) {
				BVExpr lit = null;
				for (int i = 0; i <= j; i++) {
					BVExpr temp = new BVExtract(dest, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					char character = constant.charAt(i);
					
					if (lit == null) {
						lit = new BVEq(temp, new BVConst(character));
					}
					else {
						lit = new BVAnd(lit, new BVEq(temp, new BVConst (character)));
					}
				}
				if (listOfLit == null) {
					listOfLit = lit;
				}
				else {
					listOfLit = new BVOr(listOfLit, lit);
				}
			}*/
			result = post (lit);
		}
		else {
			throw new RuntimeException("This should not be reached");
		}
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		stack1.add(loic);
		/*if (result == false) {
			//println ("[handleEdgeStartsWith] eliminate lengths");
			global_pc._addDet(elimanateCurrentLengthsConstraints());
			//println ("[handleEdgeStartsWith] " + global_pc.header.toString());
		}*/
		//println ("[handleEdgeStartsWith] returning true");
		return result;
	}
	
	//TODO: Maybe modify path condition?
	private static boolean handleEdgeNotStartsWith (EdgeNotStartsWith e) {
		//println ("[handleEdgeNotStartsWith] entered");
		if (e.getSource().getLength() < e.getDest().getLength()) return true;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			//println ("notstartswith branch 1");
			BVExpr source = getBVExpr (e.getSource());
			BVExpr dest = getBVExpr (e.getDest());
			BVExpr temp = new BVExtract(source, e.getSource().getLength() * 8 - 1, (e.getSource().getLength() - e.getDest().getLength() + 1) * 8 - 8);
			return post(new BVNot(new BVEq(temp, dest)));
		}
		else if (!e.getSource().isConstant()) {
			//println ("notstartswith branch 2");
			BVExpr source = getBVExpr(e.getSource());
			String constant = e.getDest().getSolution();
			//println ("[startsWith] constant: " + constant);
			BVExpr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				BVExpr temp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
				char character = constant.charAt(i);
				
				if (lit == null) {
					lit = new BVEq(temp, new BVConst(character));
				}
				else {
					lit = new BVAnd(lit, new BVEq(temp, new BVConst (character)));
				}
			}
			//println ("[startsWith] returning: " + lit);
			return post (new BVNot(lit));
		}
		else if (!e.getDest().isConstant()) {
			//println ("notstartswith branch 3");
			BVExpr dest = getBVExpr(e.getDest());
			String constant = e.getSource().getSolution();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
				char character = constant.charAt(i);
				lit = and(lit, new BVEq (temp, new BVConst(character)));
			}
			/*for (int j = 0; j < constant.length(); j++) {
				BVExpr lit = null;
				for (int i = 0; i <= j; i++) {
					BVExpr temp = new BVExtract(dest, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					char character = constant.charAt(i);
					
					if (lit == null) {
						lit = new BVEq(temp, new BVConst (character));
					}
					else {
						lit = new BVAnd(lit, new BVEq(temp, new BVConst (character)));
					}
				}
				if (listOfLit == null) {
					listOfLit = lit;
				}
				else {
					listOfLit = new BVOr(listOfLit, lit);
				}
			}*/
			return post (new BVNot((lit)));
		}
		else {
			String destConstant = e.getDest().getSolution();
			String sourceConstant = e.getSource().getSolution();
			return !sourceConstant.startsWith(destConstant);
		}
	}
	
	private static BVExpr endsWith (Edge e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			//println ("endswith branch 1");
			BVExpr source = getBVExpr (e.getSource());
			BVExpr dest = getBVExpr (e.getDest());
			
			BVExpr temp = new BVExtract(source, e.getDest().getLength() * 8 - 1, 0);
			return (new BVEq(temp, dest));
			
		}
		else if (!e.getSource().isConstant()) {
			//println ("endswith branch 2");
			BVExpr source = getBVExpr(e.getSource());
			String constant = e.getDest().getSolution();
			BVExpr lit = null;
			for (int i = constant.length() - 1; i >= 0; i--) {
				BVExpr temp = new BVExtract(source, (constant.length() - i) * 8 - 1, (constant.length() - i) * 8 - 8);
				char character = constant.charAt(i);
				
				if (lit == null) {
					lit = new BVEq(temp, new BVConst (character));
				}
				else {
					lit = new BVAnd(lit, new BVEq(temp, new BVConst (character)));
				}

			}
			return (lit);
		}
		else if (!e.getDest().isConstant()) {
			//println ("endswith branch 3");
			BVExpr dest = getBVExpr(e.getDest());
			String constant = e.getSource().getSolution();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
				char character = constant.charAt(i + (constant.length() - e.getDest().getLength()));
				lit = and (lit, new BVEq (temp, new BVConst (character)));
			}
			/*for (int j = 0; j < constant.length(); j++) {
				BVExpr lit = null;
				for (int i = constant.length() - 1; i >= constant.length() - j - 1; i--) {
					BVExpr temp = new BVExtract(dest, (constant.length() - i) * 8 - 1, (constant.length() - i) * 8 - 8);
					char character = constant.charAt(i);
					//boolean[] bits = toBits (character);
					if (lit == null) {
						lit = new BVEq(temp, new BVConst (character));
					}
					else {
						lit = new BVAnd(lit, new BVEq(temp, new BVConst (character)));
					}

				}
				if (listOfLit == null) {
					listOfLit = lit;
				}
				else {
					listOfLit = new BVOr(listOfLit, lit);
				}
			}*/
			return (lit);
		}
		else {
			String constant1 = e.getSource().getSolution();
			String constant2 = e.getDest().getSolution();
			if (constant1.endsWith(constant2)) {
				return new BVTrue();
			}
			else {
				return new BVFalse();
			}
		}
		//return null;
	}
	
	private static boolean handleEdgeEndsWith (EdgeEndsWith e) {
		boolean result = post (endsWith(e));
		/*if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}*/
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		stack1.add(loic);
		return result;
	}
	
	private static boolean handleEdgeNotEndsWith (EdgeNotEndsWith e) {
		//println ("Entered EdgeNotsEndsWith");
		if (e.getDest().getLength() > e.getSource().getLength()) {
			//println ("[handleEdgeNotEndsWith] return true");
			return true;
		}
		boolean result = post (new BVNot(endsWith(e)));
		/*if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}*/
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		stack1.add(loic);
		//println ("[handleEdgeNotEndsWith] return " + result);
		return result;
	}
	
	private static BVExpr equal (Edge e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());
			return new BVEq(source, dest);
		}
		else if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			String constant = e.getDest().getSolution();
			BVExpr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				char c = constant.charAt(i);
				
				BVExpr temp = new BVExtract(source, (constant.length() -i) * 8 - 1, (constant.length() -i) * 8 - 8);
				BVExpr cons = new BVConst (c);
				lit = and (lit, new BVEq(temp, cons));
			}
			return lit;
		}
		else if (!e.getDest().isConstant()) {
			BVExpr dest = getBVExpr(e.getDest());
			String constant = e.getSource().getSolution();
			BVExpr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				char c = constant.charAt(i);

				BVExpr temp = new BVExtract(dest, (constant.length() -i) * 8 - 1, (constant.length() -i) * 8 - 8);
				BVExpr cons = new BVConst (c);
				lit = and (lit, new BVEq(temp, cons));
			}
			return lit;

		}
		else {
			String constant1 = e.getSource().getSolution();
			String constant2 = e.getDest().getSolution();
			if (constant1.equals(constant2)) {
				return new BVTrue();
			} else {
				return new BVFalse();
			}
		}
		//return null;
	}
	
	
	private static boolean handleEdgeNotEqual (EdgeNotEqual e) {
		//println ("[handleEdgeNotEqual] entered");
		if (e.getSource().getLength() != e.getDest().getLength()) {
			//println ("[handleEdgeNotEqual] return true");
			return true;
		}
		//println ("[handleEdgeNotEqual] posting");
		boolean result = post (new BVNot(equal(e)));
		/*if (!result) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}*/
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		stack1.add(loic);
		return result;
	}
	
	private static boolean handleEdgeTrim (EdgeTrimEqual e) {
		//println ("[handleEdgeTrim] entered");
		if (e.getSource().getLength() == e.getDest().getLength()) {
			return post (equal(e));
		}
		boolean result = false;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());
			
			int diff = e.getSource().getLength() - e.getDest().getLength() + 1;
			
			BVExpr listOflit = null;
			for (int i = 0; i < diff; i++) {
				BVExpr lit = null;
				BVExpr sourceTemp, destTemp;
				for (int j = 0; j < i; j++) {
					sourceTemp = new BVExtract(source, (e.getSource().getLength() - j) * 8 - 1, (e.getSource().getLength() - j) * 8 - 8);
					lit = and(lit, new BVEq(sourceTemp, new BVConst(' ')));
				}
				sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i - e.getDest().getLength()) * 8 - 1 + 1);
				//destTemp = new BVExtract(dest, (e.getDest().getLength() - (j - i)) * 8 - 1, (e.getDest().getLength() - (j - i)) * 8 - 8);
				//println ("[handleEdgeTrim] 2. lit before: " + lit);
				lit = and (lit, new BVEq(sourceTemp, dest));
				//println ("[handleEdgeTrim] 2. lit so far: " + lit);
				for (int j = i + e.getDest().getLength(); j < e.getSource().getLength(); j++) {
					sourceTemp = new BVExtract(source, (e.getSource().getLength() - j) * 8 - 1, (e.getSource().getLength() - j) * 8 - 8);
					lit = and(lit, new BVEq(sourceTemp, new BVConst (' ')));
				}
				listOflit = or (listOflit, lit);
			}
			//println ("[handleEdgeTrim] 2. posting: " + listOflit);
			result = post (listOflit);

			
		}
		else if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			String constant = e.getDest().getSolution();
			int diff = e.getSource().getLength() - e.getDest().getLength() + 1;
			String allPossiblAnswers[] = new String[diff];
			for (int i = 0; i < diff; i++) {
				StringBuilder sb = new StringBuilder ();
				for (int j = 0; j < i; j++) {
					sb.append (" ");
				}
				sb.append (constant);
				for (int j = i + constant.length(); j < e.getSource().getLength(); j++) {
					sb.append (" ");
				}
				allPossiblAnswers[i] = sb.toString();
			}
			BVExpr listOfLit = null;
			for (String s: allPossiblAnswers) {
				//println ("[handleEdgeTrim] possible answer: '" + s + "'");
				BVExpr lit = null;
				for (int i = 0; i < s.length(); i++) {
					BVExpr temp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr bvconst = new BVConst (s.charAt(i));
					BVExpr toplace = new BVEq(temp, bvconst);
					if (lit == null) {
						lit = toplace;
					}
					else {
						lit = new BVAnd(lit, toplace);
					}
				}
				if (listOfLit == null) {
					listOfLit = lit;
				}
				else {
					listOfLit = new BVOr(listOfLit, lit);
				}
			}
			result = post (listOfLit);
		}
		else if (!e.getDest().isConstant()) {
			BVExpr dest = getBVExpr(e.getDest());
			String constant = e.getSource().getSolution().trim();
			if (e.getDest().getLength() != constant.length()) {
				throw new RuntimeException("Preprocessor fudged up");
			}
			BVExpr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
				lit = and (lit, new BVEq(temp, new BVConst (constant.charAt(i))));
			}
			result = post (lit);
		}
		else {
			throw new RuntimeException("This should not be reached");
		}
		/*if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}*/
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		stack1.add(loic);
		return result;
	}
	
	private static boolean handleEdgeCharAt (EdgeCharAt e) {
		boolean result = true;
		if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			char c = (char) e.getValue().solution();
			int index = e.getIndex().solutionInt();
			//println ("[handleEdgeCharAt] " + c + " " + index);
			BVExpr temp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
			BVExpr cons = new BVConst (c);
			//println ("[handleEdgeCharAt] posting: " + new BVEq(temp, cons));
			result = post (new BVEq(temp, cons));
		}
		else {
			String constant = e.getSource().getSolution();
			char c = e.getValue().solutionChar();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				BVExpr temp1 = new BVConst (constant.charAt(index));
				BVExpr temp2 = new BVConst (c);
				//println ("[handleEdgeCharAt] posting: " + new BVEq(temp1, temp2));
				result = post (new BVEq(temp1, temp2));
			}
			else {
				/*BVExpr lit = null;
				for (int i = 0; i < constant.length(); i++) {
					BVExpr temp1 = new BVConst(constant.charAt(i));
					BVExpr temp2 = new BVConst(c);
					lit = and (lit, new BVNot(new BVEq(temp1, temp2)));
				}
				result = post (lit);*/
				throw new RuntimeException("Impossible");
			}
		}
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic = new LogicalORLinearIntegerConstraints();
		LinearIntegerConstraint temp[] = new LinearIntegerConstraint[4];
		temp[0] = new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(e.getIndex().solution()));
		temp[1] = new LinearIntegerConstraint(new IntegerConstant(e.getIndex().solution()), Comparator.EQ, e.getIndex());
		temp[2] = new LinearIntegerConstraint(e.getValue(), Comparator.EQ, new IntegerConstant(e.getValue().solution()));
		temp[3] = new LinearIntegerConstraint(new IntegerConstant(e.getValue().solution()), Comparator.EQ, e.getValue());
		LinearIntegerConstraint toAdd1 = new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution()));
		LinearIntegerConstraint toAdd2 = new LinearIntegerConstraint(e.getValue(), Comparator.NE, new IntegerConstant(e.getValue().solution()));
		
		if (!(global_pc.hasConstraint(temp[0]) || global_pc.hasConstraint(temp[1]))) {
			loic.addToList(toAdd1);
		}
		else {
			//println("Not adding: " + toAdd1);
		}
		if (!(global_pc.hasConstraint(temp[2]) || global_pc.hasConstraint(temp[3]))) {
			loic.addToList(toAdd2);
		}
		else {
			//println("Not adding: " + toAdd2);
		}	
		
		loic.comment = "handleEdgeCharAt";
		stack1.add(loic);
		
		loic.addToList(toAdd1);
		
		loic.addToList(toAdd2);
		loic.comment = "handleEdgeCharAt";
		if (result == false) {
			//println ("[handleEdgeCharAt] returning false");
			//LinearOrIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			//println ("[handleEdgeCharAt] e.getSource().getLength(): " + e.getSource().getLength());
			//println ("[handleEdgeCharAt] index: " + e.getIndex().solution());
			//global_pc._addDet(loic);
		}
		return result;
	}
	
	private static boolean handleEdgeNotCharAt (EdgeNotCharAt e) {
		boolean result = true;
		if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			char c = (char) e.getValue().solution();
			int index = e.getIndex().solutionInt();
			//println ("[handleEdgeCharAt] " + c + " " + index);
			BVExpr temp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
			BVExpr cons = new BVConst (c);
			//println ("[handleEdgeCharAt] posting: " + new BVEq(temp, cons));
			result = post (new BVNot(new BVEq(temp, cons)));
		}
		else {
			String constant = e.getSource().getSolution();
			char c = e.getValue().solutionChar();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				BVExpr temp1 = new BVConst (constant.charAt(index));
				BVExpr temp2 = new BVConst (c);
				//println ("[handleEdgeCharAt] posting: " + new BVEq(temp1, temp2));
				result = post (new BVNot(new BVEq(temp1, temp2)));
			}
			else {
				/*BVExpr lit = null;
				for (int i = 0; i < constant.length(); i++) {
					BVExpr temp1 = new BVConst(constant.charAt(i));
					BVExpr temp2 = new BVConst(c);
					lit = and (lit, new BVNot(new BVEq(temp1, temp2)));
				}
				result = post (lit);*/
				throw new RuntimeException("Impossible");
			}
		}
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic = new LogicalORLinearIntegerConstraints();
		LinearIntegerConstraint temp[] = new LinearIntegerConstraint[2];
		temp[0] = new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(e.getIndex().solution()));
		temp[1] = new LinearIntegerConstraint(new IntegerConstant(e.getIndex().solution()), Comparator.EQ, e.getIndex());
		LinearIntegerConstraint toAdd1 = new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution()));
		
		if (!(global_pc.hasConstraint(temp[0]) || global_pc.hasConstraint(temp[1]))) {
			loic.addToList(toAdd1);
		}
		else {
			//println("Not adding: " + toAdd1);
		}
		
		loic.comment = "handleEdgeNotCharAt";
		stack1.add(loic);
		if (result == false) {
			//println ("[handleEdgeCharAt] returning false");
			//LinearOrIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			//println ("[handleEdgeCharAt] e.getSource().getLength(): " + e.getSource().getLength());
			//println ("[handleEdgeCharAt] index: " + e.getIndex().solution());
			//global_pc._addDet(loic);
		}
		return result;
	}
	
	private static boolean handleEdgeConcat (EdgeConcat e) {
		//println ("[handleEdgeConcat] entered");
		boolean result = false;
		if (e.getDest().isConstant()) {
			//println ("[handleEdgeConcat] dest is constant");
			if (!e.getSources().get(0).isConstant() && !e.getSources().get(1).isConstant()) {
				
				String constant = e.getDest().getSolution();
				BVExpr source1 = getBVExpr(e.getSources().get(0));
				BVExpr source2 = getBVExpr(e.getSources().get(1));
				BVExpr lit = null;
				for (int i = 0; i < e.getSources().get(0).getLength(); i++) {
					BVExpr temp = new BVExtract(source1, (e.getSources().get(0).getLength() - i) * 8 - 1, (e.getSources().get(0).getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(constant.charAt(i));
					lit = and (lit, new BVEq(temp, cons));
				}
				for (int i = 0; i < e.getSources().get(1).getLength(); i++) {
					BVExpr temp = new BVExtract(source2, (e.getSources().get(1).getLength() - i) * 8 - 1, (e.getSources().get(1).getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst (constant.charAt(i + e.getSources().get(0).getLength()));
					lit = and (lit, new BVEq(temp, cons));
				}
				result = post(lit);
			}
			else if (!e.getSources().get(0).isConstant()) {
				String destConstant = e.getDest().getSolution();
				String source2Constant = e.getSources().get(1).getSolution();
				BVExpr source1 = getBVExpr(e.getSources().get(0));
				if (!destConstant.endsWith(source2Constant)) throw new RuntimeException("This should not happen");
				BVExpr lit = null;
				for (int i = 0; i < e.getSources().get(0).getLength(); i++) {
					BVExpr temp = new BVExtract(source1, (e.getSources().get(0).getLength() - i) * 8 - 1, (e.getSources().get(0).getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst (destConstant.charAt(i));
					lit = and (lit, new BVEq(temp, cons));
				}
				result = post (lit);
			}
			else if (!e.getSources().get(1).isConstant()) {
				String destConstant = e.getDest().getSolution();
				String source1Constant = e.getSources().get(0).getSolution();
				BVExpr source2 = getBVExpr(e.getSources().get(1));
				if (!destConstant.startsWith(source1Constant)) throw new RuntimeException("This should not happen");
				BVExpr lit = null;
				for (int i = e.getSources().get(0).getLength(); i < e.getDest().getLength(); i++) {
					BVExpr temp = new BVExtract(source2, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst (destConstant.charAt(i));
					lit = and (lit, new BVEq(temp, cons));
				}
				result = post (lit);
			}
			else {
				//System.out.println(e.getDest().isConstant() + " " + e.getSources().get(1).isConstant() + " " + e.getSources().get(0).isConstant());
				String destConstant = e.getDest().getSolution();
				String source1Constant = e.getSources().get(0).getSolution();
				String source2Constant = e.getSources().get(1).getSolution();
				result = (destConstant.equals(source1Constant.concat(source2Constant)));

				//throw new RuntimeException ("Should not be reached");
			}
		}
		else {
			//println ("[handleEdgeConcat] dest is NOT constant");
			//e.getDest().isConstant() == false
			if (!e.getSources().get(0).isConstant() && !e.getSources().get(1).isConstant()) {
				//println ("[handleEdgeConcat] both sources is NOT constant");
				BVExpr source1 = getBVExpr(e.getSources().get(0));
				BVExpr source2 = getBVExpr(e.getSources().get(1));
				BVExpr dest = getBVExpr(e.getDest());
				BVExpr lit = null;
				BVExpr temp = new BVExtract(dest, (e.getDest().getLength()) * 8 - 1, (e.getDest().getLength() - e.getSources().get(0).getLength() + 1) * 8 - 8);
				lit = and (lit, new BVEq(temp, source1));
				//println ("[handleEdgeConcat] " + e.getDest().getLength() + " - " + e.getSources().get(0).getLength());
				temp = new BVExtract(dest, (e.getDest().getLength() - e.getSources().get(0).getLength()) * 8 - 1, 0);
				lit = and (lit, new BVEq(temp, source2));
				result = post(lit);
			}
			else if (!e.getSources().get(0).isConstant()) {
				BVExpr source1 = getBVExpr(e.getSources().get(0));
				String source2Cons = e.getSources().get(1).getSolution();
				BVExpr dest = getBVExpr(e.getDest());
				BVExpr lit = null;
				for (int i = 0; i < e.getSources().get(0).getLength(); i++) {
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					BVExpr sourceTemp = new BVExtract(source1, (e.getSources().get(0).getLength() - i) * 8 - 1, (e.getSources().get(0).getLength() - i) * 8 - 8);
					lit = and (lit, new BVEq(destTemp, sourceTemp));
				}
				for (int i = 0; i < source2Cons.length(); i++) {
					char character = source2Cons.charAt(i);
					BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 1, (e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(character);
					lit = and (lit, new BVEq(temp, cons));
				}
				result = post (lit);
			}
			else if (!e.getSources().get(1).isConstant()) {
				String source1Cons = e.getSources().get(0).getSolution();
				BVExpr source2 = getBVExpr(e.getSources().get(1));
				BVExpr dest = getBVExpr(e.getDest());
				BVExpr lit = null;
				for (int i = 0; i < source1Cons.length(); i++) {
					char character = source1Cons.charAt(i);
					BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst (character);
					lit = and (lit, new BVEq(temp, cons));
				}
				for (int i = 0; i < e.getSources().get(1).getLength(); i++) {
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 1, (e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 8);
					BVExpr source2Temp = new BVExtract(source2, (e.getSources().get(1).getLength() - i) * 8 - 1, (e.getSources().get(1).getLength() - i) * 8 - 8);
					lit = and (lit, new BVEq(destTemp, source2Temp));
				}
				result = post (lit);
			}
		}
		/*if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}*/
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSources().get(0).getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSources().get(0).getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getSources().get(1).getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSources().get(1).getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		stack1.add(loic);
		return result;
	}
	
	private static BVExpr contains (Edge e) {
		return contains (e, new IntegerConstant(0));
	}
	
	private static BVExpr contains (Edge e, IntegerExpression IEstartIndex) {
		int startIndex = IEstartIndex.solutionInt();
		if (startIndex < 0) startIndex = 0;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			//println ("contains branch 1");
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());
			int diff = e.getSource().getLength() - e.getDest().getLength();
			BVExpr listOfLit = null;
			for (int i = startIndex; i <= diff; i++) {
				BVExpr lit = null;
				for (int j = i; j < i + e.getDest().getLength(); j++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - j) * 8 - 1, (e.getSource().getLength() - j) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - (j - i)) * 8 - 1, (e.getDest().getLength() - (j - i)) * 8 - 8);
					lit = and (lit, new BVEq(sourceTemp, destTemp));
				}
				listOfLit = or (listOfLit, lit);
			}
			return (listOfLit);
		}
		else if (!e.getSource().isConstant()) {
			//println ("contains branch 2");
			BVExpr source = getBVExpr(e.getSource());
			String destCons = e.getDest().getSolution();
			int diff = e.getSource().getLength() - destCons.length();
			//println ("[contains] startIndex: " + startIndex);
			//println ("[contains] diff: " + diff);
			BVExpr listOfLit = null;
			for (int i = startIndex; i <= diff; i++) {
				BVExpr lit = null;
				for (int j = i; j < i + destCons.length(); j++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - j) * 8 - 1, (e.getSource().getLength() - j) * 8 - 8);
					BVExpr cons = new BVConst (destCons.charAt(j - i));
					lit = and (lit, new BVEq(sourceTemp, cons));
				}
				listOfLit = or (listOfLit, lit);
			}
			if (listOfLit == null) { //TODO: Could be sped up
				//global_pc._addDet(Comparator.GE, e.getSource().getLength(), IEstartIndex);
				return new BVFalse();
			} 
			return (listOfLit);
		}
		else if (!e.getDest().isConstant()) {
			//println ("contains branch 3");
			BVExpr dest = getBVExpr(e.getDest());
			String sourceCons = e.getSource().getSolution();
			String[] possibleSolutions = new String [e.getSource().getLength() - e.getDest().getLength() + 1 - startIndex];
			for (int i = startIndex; i <= e.getSource().getLength() - e.getDest().getLength(); i++) {
				possibleSolutions[i] = sourceCons.substring(i, i+e.getDest().getLength());
			}
			BVExpr listOfLit = null;
			for (String s: possibleSolutions) {
				BVExpr lit = null;
				for (int i = 0; i < s.length(); i++) {
					BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst (sourceCons.charAt(i));
					lit = and (lit, new BVEq(temp, cons));
				}
				listOfLit = or (listOfLit, lit);
			}
			return (listOfLit);
		}
		else {
			String constant1 = e.getSource().getSolution();
			String constant2 = e.getDest().getSolution();
			if (constant1.contains(constant2)) {
				return new BVTrue();
			}
			else {
				return new BVFalse();
			}
		}
		//return null;
	}
	
	private static boolean handleEdgeContains (EdgeContains e) {
		//println ("[handleEdgeContains] entered");
		boolean result = true;
		if (e.getSource().getLength() == e.getDest().getLength()) {
			//println ("[handleEdgeContains] handing over to equals");
			result = post (equal(e));
		}
		else {
			result = post (contains(e));
		}
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		stack1.add(loic);
		/*if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}*/
		return result;
	}
	
	private static boolean handleEdgeIndexOf2 (EdgeIndexOf2 e) {
		//println ("[handleEdgeIndexOf2] entered: " + e.toString());
		boolean result = true;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			//println ("branch 1");
			BVExpr source = getBVExpr (e.getSource());
			BVExpr dest = getBVExpr (e.getDest());
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				BVExpr totalLit = null;
				
				for (int i = e.getIndex().getMinIndex().solutionInt(); i <= index - e.getDest().getLength(); i++) {
					BVExpr lit = null;
					for (int j = 0; j < e.getDest().getLength(); j++) {
						int totalOffset = i + j;
						BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - totalOffset) * 8 - 1, (e.getSource().getLength() - totalOffset) * 8 - 8);
						BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - j) * 8 - 1, (e.getDest().getLength() - j) * 8 - 8);
						lit = and (lit, new BVEq(sourceTemp, destTemp));
					}
					totalLit = and (totalLit, new BVNot(lit));
				}
				
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - (i - index)) * 8 - 1, (e.getDest().getLength() - (i - index)) * 8 - 8);
					totalLit = and (totalLit, new BVEq(sourceTemp, destTemp));
				}
				//println ("[handleEdgeIndexOf2] posting: " + lit.toString());
				result = post (totalLit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					//println ("[handleEdgeIndexOf2] posting: " + new BVNot(equal(e)));
					result = post (new BVNot(equal(e)));
				}
				else {
					//println ("[handleEdgeIndexOf2] posting: " + new BVNot(contains(e, e.getIndex().getMinIndex().solution())));
					result = post (new BVNot(contains(e, e.getIndex().getMinIndex())));
				}
			}
		}
		else if (!e.getSource().isConstant()) {
			//println ("branch 2");
			BVExpr source = getBVExpr (e.getSource());
			String destCons = e.getDest().getSolution();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				BVExpr lit = null;
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst (destCons.charAt(i - index));
					lit = and (lit, new BVEq(sourceTemp, cons));
				}
				//println ("[handleEdgeIndexOf2] posting: " + lit.toString());
				result = post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					//println ("[handleEdgeIndexof2] posting: " + new BVNot(equal(e)));
					result = post (new BVNot(equal(e)));
				}
				else {
					//println ("[handleEdgeIndexof2] posting: " + new BVNot(contains(e, e.getIndex().getMinIndex().solution())));
					BVExpr expr= contains(e, e.getIndex().getMinIndex());
					result = post (new BVNot(expr));
				}
			}
		}
		else if (!e.getDest().isConstant()) {
			//println ("branch 3");
			String sourceCons = e.getSource().getSolution();
			
			BVExpr dest = getBVExpr(e.getDest());
			int index = e.getIndex().solutionInt();
			
			if (index > -1) {
				String realSolution = sourceCons.substring(index, index + e.getDest().getLength());
				BVExpr lit = null;
				for (int i = 0; i < realSolution.length(); i++) {
					BVExpr destExpr = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst (realSolution.charAt(i));
					lit = and (lit, new BVEq(destExpr, cons));
				}
				//println ("[handleEdgeIndexOf2] posting: " + lit.toString());
				result = post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					//println ("[handleEdgeIndexOf2] posting: " + new BVNot(equal(e)));
					result = post (new BVNot(equal(e)));
				}
				else {
					//println ("[handleEdgeIndexOf2] posting: " + new BVNot(contains(e, e.getIndex().getMinIndex().solution())));
					result = post (new BVNot(contains(e, e.getIndex().getMinIndex())));
				}
			}
		}
		else {
			throw new RuntimeException("Preprocessor should catch this");
		}
		//LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		stack1.add(loic);
		loic = elimanateCurrentLengthsConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		if (result == false) {
			//global_pc._addDet(loic);
		}
		return result;
	}
	
	private static boolean handleEdgeIndexOf (EdgeIndexOf e) {
		//println ("[handleEdgeIndexOf] entered");
		boolean result = true;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			//println ("[handleEdgeIndexOf] branch 1");
			BVExpr source = getBVExpr (e.getSource());
			BVExpr dest = getBVExpr (e.getDest());
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				/*BVExpr lit = null;
				
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - (i - index)) * 8 - 1, (e.getDest().getLength() - (i - index)) * 8 - 8);
					lit = and (lit, new BVEq(sourceTemp, destTemp));
				}
				result = post (lit);*/
				
				BVExpr totalLit = null;
				for (int i = 0; i <= index - e.getDest().getLength(); i++) { // TODO: Review
					BVExpr lit = null;
					for (int j = 0; j < e.getDest().getLength(); j++) {
						int totalOffset = i + j;
						BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - totalOffset) * 8 - 1, (e.getSource().getLength() - totalOffset) * 8 - 8);
						BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - j) * 8 - 1, (e.getDest().getLength() - j) * 8 - 8);
						lit = and (lit, new BVEq(sourceTemp, destTemp));
					}
					totalLit = and (totalLit, new BVNot(lit));
				}

				for (int i = index; i < index + e.getDest().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - (i - index)) * 8 - 1, (e.getDest().getLength() - (i - index)) * 8 - 8);
					totalLit = and (totalLit, new BVEq(sourceTemp, destTemp));
				}
				result = post (totalLit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					result = post (new BVNot(equal(e)));
				}
				else {
					result = post (new BVNot(contains(e)));
				}
				/*if (result == false) {
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				}*/
				stack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				return result;
			}
		}
		else if (!e.getSource().isConstant()) {
			//println ("[handleEdgeIndexOf] branch 2");
			BVExpr source = getBVExpr (e.getSource());
			String destCons = e.getDest().getSolution();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				//println ("[handleEdgeIndexOf] branch 2.1");
				BVExpr totalLit = null;
				//Characters before should not be equal
				for (int i = 0; i < index - destCons.length(); i++) {
					BVExpr lit = null;
					for (int j = 0; j < destCons.length(); j++) {
						int entireOff = i + j;
						BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - entireOff) * 8 - 1, (e.getSource().getLength() - entireOff) * 8 - 8);
						BVExpr cons = new BVConst(destCons.charAt(j));
						lit = and (lit, new BVEq (sourceTemp, cons));
					}
					totalLit = and(totalLit, new BVNot(lit));
				}
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(destCons.charAt(i - index));
					totalLit = and (totalLit, new BVEq(sourceTemp, cons));
				}
				result = post (totalLit);
			}
			else {
				//println ("[handleEdgeIndexOf] branch 2.2");
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					result = post (new BVNot(equal(e)));
				}
				else {
					//Check if it is at all possible
					//println ("[handleEdgeIndexOf] branch 2.2.3");
					result = post (new BVNot(contains(e)));
					//no matter if it is false, can't fix it
				}
				/*if (result == false) {
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				}*/
				stack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				return result;
			}
		}
		else if (!e.getDest().isConstant()) {
			//println ("[handleEdgeIndexOf] branch 3");
			String sourceCons = e.getSource().getSolution();
			
			BVExpr dest = getBVExpr(e.getDest());
			int index = e.getIndex().solutionInt();
			
			if (index > -1) {
				String realSolution = sourceCons.substring(index, index + e.getDest().getLength());
				BVExpr lit = null;
				for (int i = 0; i < realSolution.length(); i++) {
					BVExpr destExpr = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst (realSolution.charAt(i));
					lit = and (lit, new BVEq(destExpr, cons));
				}
				result = post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					result = post (new BVNot(equal(e)));
				}
				else {
					result = post (new BVNot(contains(e)));
				}
				/*if (result == false) {
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				}*/
				stack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				return result;
			}
		}
		else {
			//Assume both is constant
			if (e.getSource().getSolution().indexOf(e.getDest().getSolution()) == e.getIndex().solution()) {
				return true;
			}
			else {
				//global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				stack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				return false;
			}
		}
		/*if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			global_pc._addDet(loic);
		}*/
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		stack1.add(loic);
		return result;
		
	}
	
	private static boolean handleEdgeIndexOfChar (EdgeIndexOfChar e) {
		boolean result = true;
		if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				//println ("index > -1: " + index);
				BVExpr lit = null;
				/* no other occurences of the character may come before */
				for (int i = 0; i < index; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst (character);
					lit = and (lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				BVExpr constant = new BVConst (character);
				lit = and (lit, new BVEq(sourceTemp, constant));
				result = post (lit);
				//println ("[handleEdgeIndexOfChar] lit: " + lit.toString() + " " + result);
			}
			else {
				//println ("index == -1");
				BVExpr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst (character);
					lit = and (lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				result = post (lit);
				/*if (result == false) {
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				}*/
				stack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				return result;
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.indexOf(character);
			//result = post (new BVEq(new BVConst(actualAns), new BVConst(index)));
			if (actualAns == index) {
				return true;
			}
			else {return false;}
		}
		/*if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			global_pc._addDet(loic);
		}*/
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		stack1.add(loic);
		return result;
	}
	
	private static boolean handleEdgeIndexOfChar2 (EdgeIndexOfChar2 e) {
		//println ("[handleEdgeIndexOfChar2] entered: " + e.toString());
		boolean result = true;
		if (!e.getSource().isConstant()) {
			//println ("[handleEdgeIndexOfChar2] branch 1");
			BVExpr source = getBVExpr(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				//println ("[handleEdgeIndexOfChar2] branch 1.1, index="+index);
				//println (global_pc.header.toString());
				BVExpr lit = null;
				/* no other occurences of the character may come before */
				//println ("[handleEdgeIndexOfChar2] e.getIndex().getMinDist().solution() = " + e.getIndex().getMinDist().solution());
				int i = e.getIndex().getMinDist().solutionInt();
				//println ("[handleEdgeIndexOfChar2] e.getIndex().getMinDist().solution() = " + e.getIndex().getMinDist().solution());
				if (e.getIndex().getMinDist().solution() < 0) {
					i = 0;
				}
				//println ("[handleEdgeIndexOfChar2] min dist: " + i);
				for (; i < index; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst (character);
					lit = and (lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				BVExpr constant = new BVConst (character);
				lit = and (lit, new BVEq(sourceTemp, constant));
				//println ("[handleEdgeIndexOfChar2] posting: " + lit.toSMTLib());
				result = post (lit);
			}
			else {
				//println ("[handleEdgeIndexOfChar2] branch 1.2");
				BVExpr lit = null;
				int i = e.getIndex().getMinDist().solutionInt();
				if (i < 0) i = 0;
				for (; i < e.getSource().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst (character);
					lit = and (lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				result = post (lit);
			}
		}
		else {
			//println ("[handleEdgeIndexOfChar2] branch 2");
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.indexOf(character, e.getIndex().getMinDist().solutionInt());
			if (index == actualAns) {
				result = post (new BVTrue());
			}
			else {
				result = post (new BVFalse());
			}
			//result = post (new BVEq(new BVConst(actualAns), new BVConst(index)));
		}
		//LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		stack1.add(loic);
		loic = elimanateCurrentLengthsConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		if (result == false) {
			//global_pc._addDet(loic);
		}
		return result;
	}
	
	private static boolean handleEdgeNotContains (EdgeNotContains e) {
		if (e.getSource().getLength() < e.getDest().getLength()) {
			return true;
		}
		boolean result = post (new BVNot(contains(e)));
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		stack1.add(loic);
		/*if (result == false) {
			//In my automata approach this never happens
			//global_pc._addDet(elimanateCurrentLengthsConstraints());
		}*/
		return result;
	}
	
	private static boolean handleEdgeSubstring1Equal (EdgeSubstring1Equal e) {
		boolean result = false;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());
			int arg1 = e.getArgument1();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
				BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
				lit = and (lit, new BVEq(sourceTemp, destTemp));
			}
			result = post (lit);
		}
		else if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			String destCons = e.getDest().getSolution();
			int arg1 = e.getArgument1();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
				BVExpr destTemp = new BVConst (destCons.charAt(i));
				lit = and (lit, new BVEq(sourceTemp, destTemp));
			}
			result = post (lit);
		}
		else if (!e.getDest().isConstant()) {
			String sourceCons = e.getSource().getSolution();
			BVExpr dest = getBVExpr(e.getDest());
			int arg1 = e.getArgument1();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr sourceTemp = new BVConst (sourceCons.charAt(i + arg1));
				BVExpr destTemp =new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
				lit = and (lit, new BVEq (sourceTemp, destTemp));
			}
			result = post(lit);
		}
		else {
			throw new RuntimeException("Preprocessor should handle this");
		}
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		stack1.add(loic);
		/*if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}*/
		return result;
	}
	
	private static boolean handleEdgeLastIndexOfChar (EdgeLastIndexOfChar e) {
		boolean result = true;
		if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				BVExpr lit = null;
				/* no other occurences of the character may come after */
				for (int i = index+1; i < e.getSource().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst (character);
					lit = and (lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				BVExpr constant = new BVConst (character);
				lit = and (lit, new BVEq(sourceTemp, constant));
				result = post (lit);
				//println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			}
			else {
				BVExpr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst (character);
					lit = and (lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				result = post (lit);
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.indexOf(character);
			result = post (new BVEq(new BVConst(actualAns), new BVConst(index)));
		}
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		stack1.add(loic);
		/*if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			global_pc._addDet(loic);
		}*/
		return result;
	}
	
	private static boolean handleEdgeLastIndexOfChar2 (EdgeLastIndexOfChar2 e) {
		boolean result = true;
		if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				BVExpr lit = null;
				/* no other occurences of the character may come after up till second argument*/
				/*println ("minDist: " + e.getIndex().getMinDist().solution());
				//println ("index: " + index);
				//println ("e.getSource().getLength(): " + e.getSource().getLength());*/
				for (int i = index+1; i < e.getIndex().getMinDist().solution() && e.getSource().getLength() - i - 1 >= 0; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst (character);
					lit = and (lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				BVExpr constant = new BVConst (character);
				lit = and (lit, new BVEq(sourceTemp, constant));
				result = post (lit);
				//println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			}
			else {
				BVExpr lit = null;
				//Can not feature uptil the second argument
				for (int i = 0; i < e.getIndex().getMinDist().solution(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst (character);
					lit = and (lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				result = post (lit);
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.lastIndexOf(character, e.getIndex().getMinDist().solutionInt());
			result = (index == actualAns);
		}
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(e.getIndex().getMinDist().solution())));
		stack1.add(loic);
		
		/*if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			loic.addToList(new LinearIntegerConstraint(e.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(e.getIndex().getMinDist().solution())));
			global_pc._addDet(loic);
		}*/
		return result;
		
	}
	
	private static boolean handleEdgeSubstring2Equal (EdgeSubstring2Equal e) {
		boolean result = true;
		if (!e.hasSymbolicArgs()) {
			if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				BVExpr source = getBVExpr(e.getSource());
				BVExpr dest = getBVExpr(e.getDest());
				int arg1 = e.getArgument1();
				int arg2 = e.getArgument2();
				BVExpr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					lit = and (lit, new BVEq(sourceTemp, destTemp));
				}
				result = post (lit);
			}
			else if (!e.getSource().isConstant()) {
				BVExpr source = getBVExpr(e.getSource());
				String destCons = e.getDest().getSolution();
				int arg1 = e.getArgument1();
				int arg2 = e.getArgument2();
				BVExpr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
					BVExpr destTemp = new BVConst (destCons.charAt(i));
					lit = and (lit, new BVEq(sourceTemp, destTemp));
				}
				result = post (lit);
			}
			else {
				throw new RuntimeException("Preprocessor should handle this");
			}
			/*if (result == false) {
				global_pc._addDet(elimanateCurrentLengthsConstraints());
			}*/
			LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			stack1.add(loic);
			return result;
		}
		else if (e.getSymbolicArgument1() == null && e.getSymbolicArgument2() != null) {
			if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				BVExpr source = getBVExpr(e.getSource());
				BVExpr dest = getBVExpr(e.getDest());
				int arg1 = e.getArgument1();
				int arg2 = e.getSymbolicArgument2().solutionInt();
				BVExpr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					lit = and (lit, new BVEq(sourceTemp, destTemp));
				}
				result = post (lit);
			}
			else if (!e.getSource().isConstant()) {
				BVExpr source = getBVExpr(e.getSource());
				String destCons = e.getDest().getSolution();
				int arg1 = e.getArgument1();
				int arg2 = e.getSymbolicArgument2().solutionInt();
				if (arg2 - arg1 != destCons.length()) {
					//TODO: Can definitly improve here
					//LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
					loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
					loic.addToList(new LinearIntegerConstraint(e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(arg2)));
					stack1.add(loic);
					//global_pc._addDet(loic);
					return false;
					//throw new RuntimeException((arg2 - arg1) + " is not equal to '" + destCons + "' length of " + destCons.length());
				}
				BVExpr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
					BVExpr destTemp = new BVConst (destCons.charAt(i));
					lit = and (lit, new BVEq(sourceTemp, destTemp));
				}
				result = post (lit);
			}
			else {
				//Assume both constants
				if (!e.getSource().getSolution().substring(e.getArgument1(),e.getSymbolicArgument2().solutionInt()).equals((e.getDest().getSolution()))) {
					//global_pc._addDet(Comparator.NE, e.getSymbolicArgument2(), e.getSymbolicArgument2().solution());
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
					loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
					//TODO: Double check?
					loic.addToList(new LinearIntegerConstraint(e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(e.getSymbolicArgument2().solution())));
					stack1.add(loic);
					return false;
				}
			}
			if (result == false) {
				/*LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(e.getSymbolicArgument2().solution())));
				global_pc._addDet(loic);*/
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				//TODO: Double check?
				loic.addToList(new LinearIntegerConstraint(e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(e.getSymbolicArgument2().solution())));
				stack1.add(loic);
			}
			return result;
		}
		else {
			throw new RuntimeException ("not supported, yet");
		}
	}
	
	private static BVExpr and (BVExpr orig, BVExpr newE) {
		if (orig == null) {
			return newE;
		}
		else {
			return new BVAnd(orig, newE);
		}
	}
	
	private static BVExpr or (BVExpr orig, BVExpr newE) {
		if (orig == null) {
			return newE;
		}
		else {
			return new BVOr(orig, newE);
		}
	}
	
	private static boolean post (BVExpr ee) {
		
		if (ee == null) return true;
		if (expr == null) {
			expr = ee;
		}
		else {
			expr = new BVAnd(ee, expr);
		}
		//println ("Expr: " + expr);	
		//println ("[post] Formula to check: " + ee);
		//println ("[post] On top of       : " + vc.getAssumptions());
		//long timing = System.currentTimeMillis();
		try {
			StringBuffer sb = new StringBuffer ();
			sb.append ("(assert ");
			sb.append (ee.toSMTLib());
			sb.append (")");
			z3Interface.sendIncMessage(sb.toString());
		} catch (IOException e) {
			e.printStackTrace();
			System.exit(0);
		}
		//totalTiming += System.currentTimeMillis() - timing;
		Z3EverCalled = true;
		if (z3Interface.isSAT()) {
			//println ("[post]: " + vc.);
			//vc.pop();
			//println ("[post] returned true");
			return true;
		}
		else {
			//println ("[post] returned false");
			return false;
		}
	}
	
	private static boolean[] toBits (char c) {
		boolean[] result = new boolean[8];
		int num = (int) c;
		int i = result.length - 1;
		int div = 128;
		while (num > 0) {
			int temp = num / div;
			num = num - div * temp;
			div = div / 2;
			if (temp == 1) result[i] = true;
			i--;
		}
		return result;
	} 
	
	private static BVExpr getBVExpr (Vertex v){
		BVExpr result = map.get(v);
		if (result == null) {
			//8 is easier
			//result = vc.varExpr("a", vc.arrayType(vc.intType(), vc.intType()));
			result = new BVVar(v.getName(), 8 * v.getLength());
			//println ("[BVExpr] " + v.getName() +  " length: " + (8 * v.getLength()));
			map.put(v, result);
			
			try {
				BVVar var = (BVVar) result;
				//println ("Var: " + var.toSMTLibDec());
				z3Interface.sendIncMessage(var.toSMTLibDec());
			} catch (IOException e) {
				e.printStackTrace();
			}
			
			//Apply character constraints to each character
			BVExpr lit = null;
			for (int i = 0; i < v.getLength(); i++) {
				BVExpr temp = new BVExtract(result, i * 8 + 7, i * 8);
				BVExpr cons1 = new BVLT(temp, new BVConst(SymbolicStringConstraintsGeneral.MAX_CHAR));
				BVExpr cons2 = new BVNot(new BVLT(temp, new BVConst(SymbolicStringConstraintsGeneral.MIN_CHAR)));
				if (lit == null) {
					lit = new BVAnd(cons1, cons2);
				}
				else {
					lit = new BVAnd(lit, new BVAnd(cons1, cons2));
				}
			}
			post (lit);
		}
		return result;
	}
	
	private static void println (String msg) {
		System.out.println("[TranslateToZ3Inc] " + msg);
	}
	
	private static LogicalORLinearIntegerConstraints elimanateCurrentLengthsConstraints() {
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		for (Vertex v: global_graph.getVertices()) {
			if (v.isConstant() || v.getName().startsWith("CHAR")) continue;
			loic.addToList(new LinearIntegerConstraint(v.getSymbolicLength(), Comparator.NE, new IntegerConstant(v.getLength())));
		}
		return loic;
	}

}

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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.management.RuntimeErrorException;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import cvc3.Expr;
import cvc3.ExprMut;
import cvc3.FlagsMut;
import cvc3.QueryResult;
import cvc3.SatResult;
import cvc3.TypeMut;
import cvc3.ValidityChecker;

public class TranslateToCVCInc {
	
	protected static Expr expr;
	protected static ValidityChecker vc = null;
    protected static FlagsMut flags = null;
	/* This number can be calculated beforehand */
	private static final int MAXVAR = 100000;
	/* Size of string */
	private static final int MAX_SIZE_OF_STRINGS = 100;
	
	private static Map<Vertex, ExprMut> map;
	private static int vectorOffset;
	
	private static int varIndex;
	
	//public static int totalTiming = 0;
	
	private static boolean printClauses = true;
	private static boolean logging = true;
	
	private static StringGraph global_graph;
	private static PathCondition global_pc;
	
	private static boolean CVCEverCalled;
	
	private static SymbolicConstraintsGeneral scg;
	
	//most sign, first letter
	public static boolean isSat (StringGraph g, PathCondition pc) {
		if (scg == null) scg = new SymbolicConstraintsGeneral();
		CVCEverCalled = false;
		global_graph = g;
		global_pc = pc;
		expr = null;
		//println ("[isSat] Bitvector: PC passed on: " + pc.header);
		map = new HashMap<Vertex, ExprMut>();
		try{
			//if (vc == null) {
		        flags = ValidityChecker.createFlags(null);
		        flags.setFlag("dagify-exprs",false);
		        vc = ValidityChecker.create(flags);
			//}
			//else {
				//Do nothing
			//}
	       // System.out.//println("validity checker is initialized");
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
	    }
		//println ("[isSat] Walking through the edges");
		for (Edge e: g.getEdges()) {
			boolean result = handle(e);
			if (result == false) {
				if (PathCondition.flagSolved == false) {
					//println ("[isSat] Path Condition changed, starting integer solver...");
					if (scg.isSatisfiable(pc)) {
						//println ("[isSat] Found to be sat, solving...");
						scg.solve(pc);
						PathCondition.flagSolved = true;
						//println ("[isSat] solved " + global_pc.header.toString());
						vc.delete();
						return isSat (g, pc); //remove recursion
					}
					else {
						//println ("[isSat] integer solver could not solve");
						//println ("[isSat] string expr: " + expr.toString());
						//println ("[isSat] constraints: " + global_pc.header.toString());
						return false;
					}
				}
				else {
					return false;
				}
			}
		}
		if (!CVCEverCalled) {
			return true;
		}
		
		//println ("[post] Formula to check: " + vc.trueExpr());
		//println ("[post] On top of       : " + vc.getAssumptions());
		SatResult satResult = vc.checkUnsat(vc.trueExpr());
		if (satResult == SatResult.SATISFIABLE) {
			HashMap model = vc.getConcreteModel();
	    	//println(model.toString());
	    	
	    	for (Object e: model.entrySet()) {
	    		Entry entry = (Entry) e;
	    		String vertexName = entry.getKey().toString();
	    		String rawData = entry.getValue().toString();
	    		rawData = fromRawData(rawData);
	    		////println (vertexName + " = " + rawData);
	    		Vertex v = g.findVertex(vertexName);
	    		v.setSolution(rawData);
	    	}
			//println ("[isSat] Done walking through the edges");
			/* TODO: Remove*/
			vc.delete();
			return true;
		}
		else {
			vc.delete();
			return false;
		}
	}
	
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
		for (int i = 4; i < data.length(); i++) {
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
			ExprMut source = getExprMut (e.getSource());
			ExprMut dest = getExprMut (e.getDest());
			ExprMut temp = vc.newBVExtractExpr(source, e.getSource().getLength() * 8 - 1, (e.getSource().getLength() - e.getDest().getLength() + 1) * 8 - 8);
			result = post(vc.eqExpr(temp, dest));
		}
		else if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			String constant = e.getDest().getSolution();
			//println ("[startsWith] constant: " + constant);
			Expr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				ExprMut temp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
				char character = constant.charAt(i);
				boolean[] bits = toBits (character);
				if (lit == null) {
					lit = vc.eqExpr(temp, vc.newBVConstExpr(bits));
				}
				else {
					lit = vc.andExpr(lit, vc.eqExpr(temp, vc.newBVConstExpr(bits)));
				}
			}
			//println ("[startsWith] returning: " + lit);
			result = post (lit);
		}
		else if (!e.getDest().isConstant()) {
			ExprMut dest = getExprMut(e.getDest());
			String constant = e.getSource().getSolution();
			Expr listOfLit = null;
			for (int j = 0; j < constant.length(); j++) {
				Expr lit = null;
				for (int i = 0; i <= j; i++) {
					ExprMut temp = vc.newBVExtractExpr(dest, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					char character = constant.charAt(i);
					boolean[] bits = toBits (character);
					if (lit == null) {
						lit = vc.eqExpr(temp, vc.newBVConstExpr(bits));
					}
					else {
						lit = vc.andExpr(lit, vc.eqExpr(temp, vc.newBVConstExpr(bits)));
					}
				}
				if (listOfLit == null) {
					listOfLit = lit;
				}
				else {
					listOfLit = vc.orExpr(listOfLit, lit);
				}
			}
			result = post (listOfLit);
		}
		else {
			throw new RuntimeException("This should not be reached");
		}
		if (result == false) {
			//println ("[handleEdgeStartsWith] eliminate lengths");
			global_pc._addDet(elimanateCurrentLengthsConstraints());
			//println ("[handleEdgeStartsWith] " + global_pc.header.toString());
		}
		//println ("[handleEdgeStartsWith] returning true");
		return result;
	}
	
	private static boolean handleEdgeNotStartsWith (EdgeNotStartsWith e) {
		//println ("[handleEdgeNotStartsWith] entered");
		if (e.getSource().getLength() < e.getDest().getLength()) return true;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			ExprMut source = getExprMut (e.getSource());
			ExprMut dest = getExprMut (e.getDest());
			ExprMut temp = vc.newBVExtractExpr(source, e.getSource().getLength() * 8 - 1, (e.getSource().getLength() - e.getDest().getLength() + 1) * 8 - 8);
			return post(vc.notExpr(vc.eqExpr(temp, dest)));
		}
		else if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			String constant = e.getDest().getSolution();
			//println ("[startsWith] constant: " + constant);
			Expr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				ExprMut temp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
				char character = constant.charAt(i);
				boolean[] bits = toBits (character);
				if (lit == null) {
					lit = vc.eqExpr(temp, vc.newBVConstExpr(bits));
				}
				else {
					lit = vc.andExpr(lit, vc.eqExpr(temp, vc.newBVConstExpr(bits)));
				}
			}
			//println ("[startsWith] returning: " + lit);
			return post (vc.notExpr(lit));
		}
		else if (!e.getDest().isConstant()) {
			ExprMut dest = getExprMut(e.getDest());
			String constant = e.getSource().getSolution();
			Expr listOfLit = null;
			for (int j = 0; j < constant.length(); j++) {
				Expr lit = null;
				for (int i = 0; i <= j; i++) {
					ExprMut temp = vc.newBVExtractExpr(dest, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					char character = constant.charAt(i);
					boolean[] bits = toBits (character);
					if (lit == null) {
						lit = vc.eqExpr(temp, vc.newBVConstExpr(bits));
					}
					else {
						lit = vc.andExpr(lit, vc.eqExpr(temp, vc.newBVConstExpr(bits)));
					}
				}
				if (listOfLit == null) {
					listOfLit = lit;
				}
				else {
					listOfLit = vc.orExpr(listOfLit, lit);
				}
			}
			return post (vc.notExpr((listOfLit)));
		}
		else {
			String destConstant = e.getDest().getSolution();
			String sourceConstant = e.getSource().getSolution();
			return !sourceConstant.startsWith(destConstant);
		}
	}
	
	private static Expr endsWith (Edge e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			ExprMut source = getExprMut (e.getSource());
			ExprMut dest = getExprMut (e.getDest());
			
			ExprMut temp = vc.newBVExtractExpr(source, e.getDest().getLength() * 8 - 1, 0);
			return (vc.eqExpr(temp, dest));
			
		}
		else if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			String constant = e.getDest().getSolution();
			ExprMut lit = null;
			for (int i = constant.length() - 1; i >= 0; i--) {
				ExprMut temp = vc.newBVExtractExpr(source, (constant.length() - i) * 8 - 1, (constant.length() - i) * 8 - 8);
				char character = constant.charAt(i);
				boolean[] bits = toBits (character);
				if (lit == null) {
					lit = vc.eqExpr(temp, vc.newBVConstExpr(bits));
				}
				else {
					lit = vc.andExpr(lit, vc.eqExpr(temp, vc.newBVConstExpr(bits)));
				}

			}
			return (lit);
		}
		else if (!e.getDest().isConstant()) {
			ExprMut dest = getExprMut(e.getDest());
			String constant = e.getSource().getSolution();
			Expr listOfLit = null;
			for (int j = 0; j < constant.length(); j++) {
				Expr lit = null;
				for (int i = constant.length() - 1; i >= constant.length() - j - 1; i--) {
					ExprMut temp = vc.newBVExtractExpr(dest, (constant.length() - i) * 8 - 1, (constant.length() - i) * 8 - 8);
					char character = constant.charAt(i);
					boolean[] bits = toBits (character);
					if (lit == null) {
						lit = vc.eqExpr(temp, vc.newBVConstExpr(bits));
					}
					else {
						lit = vc.andExpr(lit, vc.eqExpr(temp, vc.newBVConstExpr(bits)));
					}

				}
				if (listOfLit == null) {
					listOfLit = lit;
				}
				else {
					listOfLit = vc.orExpr(listOfLit, lit);
				}
			}
			return (listOfLit);
		}
		return null;
	}
	
	private static boolean handleEdgeEndsWith (EdgeEndsWith e) {
		boolean result = post (endsWith(e));
		if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}
		return result;
	}
	
	private static boolean handleEdgeNotEndsWith (EdgeNotEndsWith e) {
		if (e.getDest().getLength() > e.getSource().getLength()) {
			return true;
		}
		boolean result = post (vc.notExpr(endsWith(e)));
		if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}
		return result;
	}
	
	private static Expr equal (Edge e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			ExprMut dest = getExprMut(e.getDest());
			return vc.eqExpr(source, dest);
		}
		else if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			String constant = e.getDest().getSolution();
			Expr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				char c = constant.charAt(i);
				boolean[] bits = toBits(c);
				ExprMut temp = vc.newBVExtractExpr(source, (constant.length() -i) * 8 - 1, (constant.length() -i) * 8 - 8);
				Expr cons = vc.newBVConstExpr(bits);
				lit = and (lit, vc.eqExpr(temp, cons));
			}
			return lit;
		}
		else if (!e.getDest().isConstant()) {
			ExprMut dest = getExprMut(e.getDest());
			String constant = e.getSource().getSolution();
			Expr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				char c = constant.charAt(i);
				boolean[] bits = toBits(c);
				ExprMut temp = vc.newBVExtractExpr(dest, (constant.length() -i) * 8 - 1, (constant.length() -i) * 8 - 8);
				Expr cons = vc.newBVConstExpr(bits);
				lit = and (lit, vc.eqExpr(temp, cons));
			}
			return lit;

		}
		return null;
	}
	
	
	private static boolean handleEdgeNotEqual (EdgeNotEqual e) {
		//println ("[handleEdgeNotEqual] entered");
		if (e.getSource().getLength() != e.getDest().getLength()) {
			return true;
		}
		
		return post (vc.notExpr(equal(e)));
	}
	
	private static boolean handleEdgeTrim (EdgeTrimEqual e) {
		//println ("[handleEdgeTrim] entered");
		if (e.getSource().getLength() == e.getDest().getLength()) {
			return post (equal(e));
		}
		boolean result = false;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			ExprMut dest = getExprMut(e.getDest());
			
			int diff = e.getSource().getLength() - e.getDest().getLength() + 1;
			
			Expr listOflit = null;
			for (int i = 0; i < diff; i++) {
				Expr lit = null;
				ExprMut sourceTemp, destTemp;
				for (int j = 0; j < i; j++) {
					sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - j) * 8 - 1, (e.getSource().getLength() - j) * 8 - 8);
					lit = and(lit, vc.eqExpr(sourceTemp, vc.newBVConstExpr(toBits(' '))));
				}
				sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i - e.getDest().getLength()) * 8 - 1 + 1);
				//destTemp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - (j - i)) * 8 - 1, (e.getDest().getLength() - (j - i)) * 8 - 8);
				//println ("[handleEdgeTrim] 2. lit before: " + lit);
				lit = and (lit, vc.eqExpr(sourceTemp, dest));
				//println ("[handleEdgeTrim] 2. lit so far: " + lit);
				for (int j = i + e.getDest().getLength(); j < e.getSource().getLength(); j++) {
					sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - j) * 8 - 1, (e.getSource().getLength() - j) * 8 - 8);
					lit = and(lit, vc.eqExpr(sourceTemp, vc.newBVConstExpr(toBits(' '))));
				}
				listOflit = or (listOflit, lit);
			}
			//println ("[handleEdgeTrim] 2. posting: " + listOflit);
			result = post (listOflit);

			
		}
		else if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
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
			Expr listOfLit = null;
			for (String s: allPossiblAnswers) {
				//println ("[handleEdgeTrim] possible answer: '" + s + "'");
				Expr lit = null;
				for (int i = 0; i < s.length(); i++) {
					Expr temp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr bvconst = vc.newBVConstExpr(toBits(s.charAt(i)));
					Expr toplace = vc.eqExpr(temp, bvconst);
					if (lit == null) {
						lit = toplace;
					}
					else {
						lit = vc.andExpr(lit, toplace);
					}
				}
				if (listOfLit == null) {
					listOfLit = lit;
				}
				else {
					listOfLit = vc.orExpr(listOfLit, lit);
				}
			}
			result = post (listOfLit);
		}
		else if (!e.getDest().isConstant()) {
			Expr dest = getExprMut(e.getDest());
			String constant = e.getSource().getSolution().trim();
			if (e.getDest().getLength() != constant.length()) {
				throw new RuntimeException("Preprocessor fudged up");
			}
			Expr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				Expr temp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
				lit = and (lit, vc.eqExpr(temp, vc.newBVConstExpr(toBits(constant.charAt(i)))));
			}
			result = post (lit);
		}
		else {
			throw new RuntimeException("This should not be reached");
		}
		if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}
		return result;
	}
	
	private static boolean handleEdgeCharAt (EdgeCharAt e) {
		boolean result = true;
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			char c = (char) e.getValue().solutionInt();
			int index = e.getIndex().solutionInt();
			//println ("[handleEdgeCharAt] " + c + " " + index);
			Expr temp = vc.newBVExtractExpr(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
			Expr cons = vc.newBVConstExpr(toBits(c));
			//println ("[handleEdgeCharAt] posting: " + vc.eqExpr(temp, cons));
			result = post (vc.eqExpr(temp, cons));
		}
		else {
			String constant = e.getSource().getSolution();
			char c = (char) e.getValue().solutionInt();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				ExprMut temp1 = vc.newBVConstExpr(toBits(constant.charAt(index)));
				ExprMut temp2 = vc.newBVConstExpr(toBits(c));
				//println ("[handleEdgeCharAt] posting: " + vc.eqExpr(temp1, temp2));
				result = post (vc.eqExpr(temp1, temp2));
			}
			else {
				Expr lit = null;
				for (int i = 0; i < constant.length(); i++) {
					ExprMut temp1 = vc.newBVConstExpr(toBits(constant.charAt(i)));
					ExprMut temp2 = vc.newBVConstExpr(toBits(c));
					lit = and (lit, vc.notExpr(vc.eqExpr(temp1, temp2)));
				}
				//println ("[handleEdgeCharAt] posting: " + lit.toString());
				result = post (lit);
			}
		}
		if (result == false) {
			//println ("[handleEdgeCharAt] returning false");
			//LinearOrIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			//println ("[handleEdgeCharAt] e.getSource().getLength(): " + e.getSource().getLength());
			//println ("[handleEdgeCharAt] index: " + e.getIndex().solutionInt());
			LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			loic.addToList(new LinearIntegerConstraint(e.getValue(), Comparator.NE, new IntegerConstant(e.getValue().solution())));
			global_pc._addDet(loic);
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
				ExprMut source1 = getExprMut(e.getSources().get(0));
				ExprMut source2 = getExprMut(e.getSources().get(1));
				Expr lit = null;
				for (int i = 0; i < e.getSources().get(0).getLength(); i++) {
					Expr temp = vc.newBVExtractExpr(source1, (e.getSources().get(0).getLength() - i) * 8 - 1, (e.getSources().get(0).getLength() - i) * 8 - 8);
					Expr cons = vc.newBVConstExpr(toBits(constant.charAt(i)));
					lit = and (lit, vc.eqExpr(temp, cons));
				}
				for (int i = 0; i < e.getSources().get(1).getLength(); i++) {
					Expr temp = vc.newBVExtractExpr(source2, (e.getSources().get(1).getLength() - i) * 8 - 1, (e.getSources().get(1).getLength() - i) * 8 - 8);
					Expr cons = vc.newBVConstExpr(toBits(constant.charAt(i + e.getSources().get(0).getLength())));
					lit = and (lit, vc.eqExpr(temp, cons));
				}
				result = post(lit);
			}
			else if (!e.getSources().get(0).isConstant()) {
				String destConstant = e.getDest().getSolution();
				String source2Constant = e.getSources().get(1).getSolution();
				ExprMut source1 = getExprMut(e.getSources().get(0));
				if (!destConstant.endsWith(source2Constant)) throw new RuntimeException("This should not happen");
				Expr lit = null;
				for (int i = 0; i < e.getSources().get(0).getLength(); i++) {
					ExprMut temp = vc.newBVExtractExpr(source1, (e.getSources().get(0).getLength() - i) * 8 - 1, (e.getSources().get(0).getLength() - i) * 8 - 8);
					ExprMut cons = vc.newBVConstExpr(toBits(destConstant.charAt(i)));
					lit = and (lit, vc.eqExpr(temp, cons));
				}
				result = post (lit);
			}
			else if (!e.getSources().get(1).isConstant()) {
				String destConstant = e.getDest().getSolution();
				String source1Constant = e.getSources().get(0).getSolution();
				ExprMut source2 = getExprMut(e.getSources().get(1));
				if (!destConstant.startsWith(source1Constant)) throw new RuntimeException("This should not happen");
				Expr lit = null;
				for (int i = e.getSources().get(0).getLength(); i < e.getDest().getLength(); i++) {
					ExprMut temp = vc.newBVExtractExpr(source2, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					ExprMut cons = vc.newBVConstExpr(toBits(destConstant.charAt(i)));
					lit = and (lit, vc.eqExpr(temp, cons));
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
				ExprMut source1 = getExprMut(e.getSources().get(0));
				ExprMut source2 = getExprMut(e.getSources().get(1));
				ExprMut dest = getExprMut(e.getDest());
				Expr lit = null;
				Expr temp = vc.newBVExtractExpr(dest, (e.getDest().getLength()) * 8 - 1, (e.getDest().getLength() - e.getSources().get(0).getLength() + 1) * 8 - 8);
				lit = and (lit, vc.eqExpr(temp, source1));
				//println ("[handleEdgeConcat] " + e.getDest().getLength() + " - " + e.getSources().get(0).getLength());
				temp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - e.getSources().get(0).getLength()) * 8 - 1, 0);
				lit = and (lit, vc.eqExpr(temp, source2));
				result = post(lit);
			}
			else if (!e.getSources().get(0).isConstant()) {
				ExprMut source1 = getExprMut(e.getSources().get(0));
				String source2Cons = e.getSources().get(1).getSolution();
				ExprMut dest = getExprMut(e.getDest());
				Expr lit = null;
				for (int i = 0; i < e.getSources().get(0).getLength(); i++) {
					Expr destTemp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					Expr sourceTemp = vc.newBVExtractExpr(source1, (e.getSources().get(0).getLength() - i) * 8 - 1, (e.getSources().get(0).getLength() - i) * 8 - 8);
					lit = and (lit, vc.eqExpr(destTemp, sourceTemp));
				}
				for (int i = 0; i < source2Cons.length(); i++) {
					char character = source2Cons.charAt(i);
					Expr temp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 1, (e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 8);
					Expr cons = vc.newBVConstExpr(toBits (character));
					lit = and (lit, vc.eqExpr(temp, cons));
				}
				result = post (lit);
			}
			else if (!e.getSources().get(1).isConstant()) {
				String source1Cons = e.getSources().get(0).getSolution();
				ExprMut source2 = getExprMut(e.getSources().get(1));
				ExprMut dest = getExprMut(e.getDest());
				Expr lit = null;
				for (int i = 0; i < source1Cons.length(); i++) {
					char character = source1Cons.charAt(i);
					Expr temp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					Expr cons = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.eqExpr(temp, cons));
				}
				for (int i = 0; i < e.getSources().get(1).getLength(); i++) {
					Expr destTemp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 1, (e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 8);
					Expr source2Temp = vc.newBVExtractExpr(source2, (e.getSources().get(1).getLength() - i) * 8 - 1, (e.getSources().get(1).getLength() - i) * 8 - 8);
					lit = and (lit, vc.eqExpr(destTemp, source2Temp));
				}
				result = post (lit);
			}
		}
		if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}
		return result;
	}
	
	private static Expr contains (Edge e) {
		return contains (e, 0);
	}
	
	private static Expr contains (Edge e, int startIndex) {
		if (startIndex < 0) startIndex = 0;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			ExprMut dest = getExprMut(e.getDest());
			int diff = e.getSource().getLength() - e.getDest().getLength();
			Expr listOfLit = null;
			for (int i = startIndex; i <= diff; i++) {
				Expr lit = null;
				for (int j = i; j < i + e.getDest().getLength(); j++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - j) * 8 - 1, (e.getSource().getLength() - j) * 8 - 8);
					Expr destTemp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - (j - i)) * 8 - 1, (e.getDest().getLength() - (j - i)) * 8 - 8);
					lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
				}
				listOfLit = or (listOfLit, lit);
			}
			return (listOfLit);
		}
		else if (!e.getSource().isConstant()) {
			//println ("[contains] source not constant");
			ExprMut source = getExprMut(e.getSource());
			String destCons = e.getDest().getSolution();
			int diff = e.getSource().getLength() - destCons.length();
			//println ("[contains] diff: " + diff);
			Expr listOfLit = null;
			for (int i = startIndex; i <= diff; i++) {
				Expr lit = null;
				for (int j = i; j < i + destCons.length(); j++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - j) * 8 - 1, (e.getSource().getLength() - j) * 8 - 8);
					Expr cons = vc.newBVConstExpr(toBits (destCons.charAt(j - i)));
					lit = and (lit, vc.eqExpr(sourceTemp, cons));
				}
				listOfLit = or (listOfLit, lit);
			}
			return (listOfLit);
		}
		else if (!e.getDest().isConstant()) {
			ExprMut dest = getExprMut(e.getDest());
			String sourceCons = e.getSource().getSolution();
			String[] possibleSolutions = new String [e.getSource().getLength() - e.getDest().getLength() + 1 - startIndex];
			for (int i = startIndex; i <= e.getSource().getLength() - e.getDest().getLength(); i++) {
				possibleSolutions[i] = sourceCons.substring(i, i+e.getDest().getLength());
			}
			Expr listOfLit = null;
			for (String s: possibleSolutions) {
				Expr lit = null;
				for (int i = 0; i < s.length(); i++) {
					Expr temp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					Expr cons = vc.newBVConstExpr(toBits(sourceCons.charAt(i)));
					lit = and (lit, vc.eqExpr(temp, cons));
				}
				listOfLit = or (listOfLit, lit);
			}
			return (listOfLit);
		}
		return null;
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
		if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}
		return result;
	}
	
	private static boolean handleEdgeIndexOf2 (EdgeIndexOf2 e) {
		//println ("[handleEdgeIndexOf2] entered: " + e.toString());
		boolean result = true;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			ExprMut source = getExprMut (e.getSource());
			ExprMut dest = getExprMut (e.getDest());
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				Expr lit = null;
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					ExprMut sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					ExprMut destTemp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - (i - index)) * 8 - 1, (e.getDest().getLength() - (i - index)) * 8 - 8);
					lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
				}
				//println ("[handleEdgeIndexOf2] posting: " + lit.toString());
				result = post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					//println ("[handleEdgeIndexOf2] posting: " + vc.notExpr(equal(e)));
					result = post (vc.notExpr(equal(e)));
				}
				else {
					//println ("[handleEdgeIndexOf2] posting: " + vc.notExpr(contains(e, e.getIndex().getMinIndex().solutionInt())));
					result = post (vc.notExpr(contains(e, e.getIndex().getMinIndex().solutionInt())));
				}
			}
		}
		else if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut (e.getSource());
			String destCons = e.getDest().getSolution();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				Expr lit = null;
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					ExprMut sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					ExprMut cons = vc.newBVConstExpr(toBits(destCons.charAt(i - index)));
					lit = and (lit, vc.eqExpr(sourceTemp, cons));
				}
				//println ("[handleEdgeIndexOf2] posting: " + lit.toString());
				result = post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					//println ("[handleEdgeIndexof2] posting: " + vc.notExpr(equal(e)));
					result = post (vc.notExpr(equal(e)));
				}
				else {
					//println ("[handleEdgeIndexof2] posting: " + vc.notExpr(contains(e, e.getIndex().getMinIndex().solutionInt())));
					result = post (vc.notExpr(contains(e, e.getIndex().getMinIndex().solutionInt())));
				}
			}
		}
		else if (!e.getDest().isConstant()) {
			String sourceCons = e.getSource().getSolution();
			
			ExprMut dest = getExprMut(e.getDest());
			int index = e.getIndex().solutionInt();
			
			if (index > -1) {
				String realSolution = sourceCons.substring(index, index + e.getDest().getLength());
				Expr lit = null;
				for (int i = 0; i < realSolution.length(); i++) {
					ExprMut destExpr = vc.newBVExtractExpr(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					ExprMut cons = vc.newBVConstExpr(toBits(realSolution.charAt(i)));
					lit = and (lit, vc.eqExpr(destExpr, cons));
				}
				//println ("[handleEdgeIndexOf2] posting: " + lit.toString());
				result = post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					//println ("[handleEdgeIndexOf2] posting: " + vc.notExpr(equal(e)));
					result = post (vc.notExpr(equal(e)));
				}
				else {
					//println ("[handleEdgeIndexOf2] posting: " + vc.notExpr(contains(e, e.getIndex().getMinIndex().solutionInt())));
					result = post (vc.notExpr(contains(e, e.getIndex().getMinIndex().solutionInt())));
				}
			}
		}
		if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			global_pc._addDet(loic);
		}
		return result;
	}
	
	private static boolean handleEdgeIndexOf (EdgeIndexOf e) {
		//println ("[handleEdgeIndexOf] entered");
		boolean result = true;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			//println ("[handleEdgeIndexOf] branch 1");
			ExprMut source = getExprMut (e.getSource());
			ExprMut dest = getExprMut (e.getDest());
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				Expr lit = null;
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					ExprMut sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					ExprMut destTemp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - (i - index)) * 8 - 1, (e.getDest().getLength() - (i - index)) * 8 - 8);
					lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
				}
				result = post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					result = post (vc.notExpr(equal(e)));
				}
				else {
					result = post (vc.notExpr(contains(e)));
				}
				if (result == false) {
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				}
				return result;
			}
		}
		else if (!e.getSource().isConstant()) {
			//println ("[handleEdgeIndexOf] branch 2");
			ExprMut source = getExprMut (e.getSource());
			String destCons = e.getDest().getSolution();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				//println ("[handleEdgeIndexOf] branch 2.1");
				Expr lit = null;
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					ExprMut sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					ExprMut cons = vc.newBVConstExpr(toBits(destCons.charAt(i - index)));
					lit = and (lit, vc.eqExpr(sourceTemp, cons));
				}
				result = post (lit);
			}
			else {
				//println ("[handleEdgeIndexOf] branch 2.2");
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					result = post (vc.notExpr(equal(e)));
				}
				else {
					//Check if it is at all possible
					//println ("[handleEdgeIndexOf] branch 2.2.3");
					result = post (vc.notExpr(contains(e)));
					//no matter if it is false, can't fix it
				}
				if (result == false) {
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				}
				return result;
			}
		}
		else if (!e.getDest().isConstant()) {
			//println ("[handleEdgeIndexOf] branch 3");
			String sourceCons = e.getSource().getSolution();
			
			ExprMut dest = getExprMut(e.getDest());
			int index = e.getIndex().solutionInt();
			
			if (index > -1) {
				String realSolution = sourceCons.substring(index, index + e.getDest().getLength());
				Expr lit = null;
				for (int i = 0; i < realSolution.length(); i++) {
					ExprMut destExpr = vc.newBVExtractExpr(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					ExprMut cons = vc.newBVConstExpr(toBits(realSolution.charAt(i)));
					lit = and (lit, vc.eqExpr(destExpr, cons));
				}
				result = post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return true;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					result = post (vc.notExpr(equal(e)));
				}
				else {
					result = post (vc.notExpr(contains(e)));
				}
				if (result == false) {
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				}
				return result;
			}
		}
		else {
			throw new RuntimeException("Should not be reached");
		}
		if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			global_pc._addDet(loic);
		}
		return result;
		
	}
	
	private static boolean handleEdgeIndexOfChar (EdgeIndexOfChar e) {
		boolean result = true;
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solutionInt();
			if (index > -1) {
				Expr lit = null;
				/* no other occurences of the character may come before */
				for (int i = 0; i < index; i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				Expr constant = vc.newBVConstExpr(toBits(character));
				lit = and (lit, vc.eqExpr(sourceTemp, constant));
				result = post (lit);
				//println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			}
			else {
				Expr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				result = post (lit);
				if (result == false) {
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				}
				return result;
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solutionInt();
			int actualAns = source.indexOf(character);
			result = post (vc.eqExpr(vc.ratExpr(actualAns), vc.ratExpr(index)));
		}
		if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			global_pc._addDet(loic);
		}
		return result;
	}
	
	private static boolean handleEdgeIndexOfChar2 (EdgeIndexOfChar2 e) {
		//println ("[handleEdgeIndexOfChar2] entered: " + e.toString());
		boolean result = true;
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solutionInt();
			if (index > -1) {
				//println ("[handleEdgeIndexOfChar2] branch 1");
				Expr lit = null;
				/* no other occurences of the character may come before */
				//println ("[handleEdgeIndexOfChar2] e.getIndex().getMinDist().solutionInt() = " + e.getIndex().getMinDist().solutionInt());
				int i = e.getIndex().getMinDist().solutionInt();
				if (e.getIndex().getMinDist().solutionInt() < 0) {
					i = 0;
				}
				//println ("[handleEdgeIndexOfChar2] min dist: " + i);
				for (; i < index; i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				Expr constant = vc.newBVConstExpr(toBits(character));
				lit = and (lit, vc.eqExpr(sourceTemp, constant));
				//println ("[handleEdgeIndexOfChar2] posting: " + lit.toString());
				result = post (lit);
			}
			else {
				Expr lit = null;
				int i = e.getIndex().getMinDist().solutionInt();
				if (i < 0) i = 0;
				for (; i < e.getSource().getLength(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				result = post (lit);
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solutionInt();
			int actualAns = source.indexOf(character, e.getIndex().getMinDist().solutionInt());
			result = post (vc.eqExpr(vc.ratExpr(actualAns), vc.ratExpr(index)));
		}
		if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			global_pc._addDet(loic);
		}
		return result;
	}
	
	private static boolean handleEdgeNotContains (EdgeNotContains e) {
		if (e.getSource().getLength() < e.getDest().getLength()) {
			return true;
		}
		boolean result = post (vc.notExpr(contains(e)));
		if (result == false) {
			//In my automata approach this never happens
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}
		return result;
	}
	
	private static boolean handleEdgeSubstring1Equal (EdgeSubstring1Equal e) {
		boolean result = false;
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			ExprMut dest = getExprMut(e.getDest());
			int arg1 = e.getArgument1();
			Expr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
				Expr destTemp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
				lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
			}
			result = post (lit);
		}
		else if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			String destCons = e.getDest().getSolution();
			int arg1 = e.getArgument1();
			Expr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
				Expr destTemp = vc.newBVConstExpr(toBits(destCons.charAt(i)));
				lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
			}
			result = post (lit);
		}
		else {
			throw new RuntimeException("Preprocessor should handle this");
		}
		if (result == false) {
			global_pc._addDet(elimanateCurrentLengthsConstraints());
		}
		return result;
	}
	
	private static boolean handleEdgeLastIndexOfChar (EdgeLastIndexOfChar e) {
		boolean result = true;
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solutionInt();
			if (index > -1) {
				Expr lit = null;
				/* no other occurences of the character may come after */
				for (int i = index+1; i < e.getSource().getLength(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				Expr constant = vc.newBVConstExpr(toBits(character));
				lit = and (lit, vc.eqExpr(sourceTemp, constant));
				result = post (lit);
				//println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			}
			else {
				Expr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				result = post (lit);
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solutionInt();
			int actualAns = source.indexOf(character);
			result = post (vc.eqExpr(vc.ratExpr(actualAns), vc.ratExpr(index)));
		}
		if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			global_pc._addDet(loic);
		}
		return result;
	}
	
	private static boolean handleEdgeLastIndexOfChar2 (EdgeLastIndexOfChar2 e) {
		boolean result = true;
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solutionInt();
			if (index > -1) {
				Expr lit = null;
				/* no other occurences of the character may come after up till second argument*/
				for (int i = index+1; i < e.getIndex().getMinDist().solutionInt(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				Expr constant = vc.newBVConstExpr(toBits(character));
				lit = and (lit, vc.eqExpr(sourceTemp, constant));
				result = post (lit);
				//println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			}
			else {
				Expr lit = null;
				//Can not feature uptil the second argument
				for (int i = 0; i < e.getIndex().getMinDist().solutionInt(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				result = post (lit);
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solutionInt();
			int actualAns = source.lastIndexOf(character, e.getIndex().getMinDist().solutionInt());
			result = (index == actualAns);
		}
		if (result == false) {
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
			loic.addToList(new LinearIntegerConstraint(e.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(e.getIndex().getMinDist().solutionInt())));
			global_pc._addDet(loic);
		}
		return result;
		
	}
	
	private static boolean handleEdgeSubstring2Equal (EdgeSubstring2Equal e) {
		boolean result = true;
		if (!e.hasSymbolicArgs()) {
			if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				ExprMut source = getExprMut(e.getSource());
				ExprMut dest = getExprMut(e.getDest());
				int arg1 = e.getArgument1();
				int arg2 = e.getArgument2();
				Expr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
					Expr destTemp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
				}
				result = post (lit);
			}
			else if (!e.getSource().isConstant()) {
				ExprMut source = getExprMut(e.getSource());
				String destCons = e.getDest().getSolution();
				int arg1 = e.getArgument1();
				int arg2 = e.getArgument2();
				Expr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
					Expr destTemp = vc.newBVConstExpr(toBits(destCons.charAt(i)));
					lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
				}
				result = post (lit);
			}
			else {
				throw new RuntimeException("Preprocessor should handle this");
			}
			if (result == false) {
				global_pc._addDet(elimanateCurrentLengthsConstraints());
			}
			return result;
		}
		else if (e.getSymbolicArgument1() == null && e.getSymbolicArgument2() != null) {
			if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				ExprMut source = getExprMut(e.getSource());
				ExprMut dest = getExprMut(e.getDest());
				int arg1 = e.getArgument1();
				int arg2 = e.getSymbolicArgument2().solutionInt();
				Expr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
					Expr destTemp = vc.newBVExtractExpr(dest, (e.getDest().getLength() - i) * 8 - 1, (e.getDest().getLength() - i) * 8 - 8);
					lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
				}
				result = post (lit);
			}
			else if (!e.getSource().isConstant()) {
				ExprMut source = getExprMut(e.getSource());
				String destCons = e.getDest().getSolution();
				int arg1 = e.getArgument1();
				int arg2 = e.getSymbolicArgument2().solutionInt();
				if (arg2 - arg1 != destCons.length()) {
					//TODO: Can definitly improve here
					LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
					loic.addToList(new LinearIntegerConstraint(e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(arg2)));
					global_pc._addDet(loic);
					return false;
					//throw new RuntimeException((arg2 - arg1) + " is not equal to '" + destCons + "' length of " + destCons.length());
				}
				Expr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
					Expr destTemp = vc.newBVConstExpr(toBits(destCons.charAt(i)));
					lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
				}
				result = post (lit);
			}
			else {
				throw new RuntimeException("Preprocessor should handle this");
			}
			if (result == false) {
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(e.getSymbolicArgument2().solution())));
				global_pc._addDet(loic);
			}
			return result;
		}
		else {
			throw new RuntimeException ("not supported, yet");
		}
	}
	
	private static Expr and (Expr orig, Expr newE) {
		if (orig == null) {
			return newE;
		}
		else {
			return vc.andExpr(orig, newE);
		}
	}
	
	private static Expr or (Expr orig, Expr newE) {
		if (orig == null) {
			return newE;
		}
		else {
			return vc.orExpr(orig, newE);
		}
	}
	
	private static boolean post (Expr ee) {
		if (expr == null) {
			expr = ee;
		}
		else {
			expr = vc.andExpr(ee, expr);
		}
		
		vc.push();	
		//println ("[post] Formula to check: " + ee);
		//println ("[post] On top of       : " + vc.getAssumptions());
		//long timing = System.currentTimeMillis();
		SatResult satResult = vc.checkUnsat(ee);
		//totalTiming += System.currentTimeMillis() - timing;
		CVCEverCalled = true;
		if (satResult == SatResult.SATISFIABLE) {
			//println ("[post]: " + vc.);
			//vc.pop();
			//println ("[post] returned true");
			vc.pop();
			vc.assertFormula(ee);
			return true;
		}
		else {
			vc.pop();
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
	
	private static ExprMut getExprMut (Vertex v){
		ExprMut result = map.get(v);
		if (result == null) {
			//8 is easier
			//result = vc.varExpr("a", vc.arrayType(vc.intType(), vc.intType()));
			result = vc.varExpr(v.getName(), vc.bitvecType(8 * v.getLength()));
			//println ("[ExprMut] " + v.getName() +  " length: " + (8 * v.getLength()));
			map.put(v, result);
			//Apply character constraints to each character
			Expr lit = null;
			for (int i = 0; i < v.getLength(); i++) {
				Expr temp = vc.newBVExtractExpr(result, i * 8 + 7, i * 8);
				Expr cons1 = vc.newBVLTExpr(temp, vc.newBVConstExpr(toBits((char)SymbolicStringConstraintsGeneral.MAX_CHAR)));
				Expr cons2 = vc.notExpr(vc.newBVLTExpr(temp, vc.newBVConstExpr(toBits((char)SymbolicStringConstraintsGeneral.MIN_CHAR))));
				if (lit == null) {
					lit = vc.andExpr(cons1, cons2);
				}
				else {
					lit = vc.andExpr(lit, vc.andExpr(cons1, cons2));
				}
			}
			post (lit);
		}
		return result;
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

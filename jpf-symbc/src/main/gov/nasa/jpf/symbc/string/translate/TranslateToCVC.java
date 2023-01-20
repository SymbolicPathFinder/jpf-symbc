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
import gov.nasa.jpf.symbc.string.graph.EdgeLastIndexOfChar;
import gov.nasa.jpf.symbc.string.graph.EdgeLastIndexOfChar2;
import gov.nasa.jpf.symbc.string.graph.EdgeNotContains;
import gov.nasa.jpf.symbc.string.graph.EdgeNotEndsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeNotEqual;
import gov.nasa.jpf.symbc.string.graph.EdgeNotStartsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeReplaceCharChar;
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

public class TranslateToCVC {
	
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
	
	private static SymbolicConstraintsGeneral scg;
	
	private static PathCondition global_pc;
	
	//most sign, first letter
	public static boolean isSat (StringGraph g, PathCondition pc) {
		/* check if there was a timeout */
		SymbolicStringConstraintsGeneral.checkTimeOut();
		//println ("[isSat] graph after preprocessing: " + g.toDot());
		global_pc = pc;
		if (scg == null) scg = new SymbolicConstraintsGeneral();
		expr = null;
		//println ("[isSat] Bitvector: PC passed on: " + pc.header);
		map = new HashMap<Vertex, ExprMut>();
		try{
	        flags = ValidityChecker.createFlags(null);
	        flags.setFlag("dagify-exprs",false);
	        vc = ValidityChecker.create(flags);
	       // System.out.//println("validity checker is initialized");
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
	    }
		//println ("[isSat] Walking through the edges");
		for (Edge e: g.getEdges()) {
			if (e instanceof EdgeStartsWith) {
				handleEdgeStartsWith ((EdgeStartsWith) e);
			}
			else if (e instanceof EdgeNotStartsWith) {
				handleEdgeNotStartsWith((EdgeNotStartsWith) e);
			}
			else if (e instanceof EdgeEqual) {
				handleEdgeEqual ((EdgeEqual) e);
			}
			else if (e instanceof EdgeNotEqual) {
				handleEdgeNotEqual((EdgeNotEqual) e);
			}
			else if (e instanceof EdgeTrimEqual) {
				handleEdgeTrim((EdgeTrimEqual) e);
			}
			else if (e instanceof EdgeCharAt) {
				handleEdgeCharAt((EdgeCharAt) e);
			}
			else if (e instanceof EdgeConcat) {
				handleEdgeConcat((EdgeConcat) e);
			}
			else if (e instanceof EdgeContains) {
				handleEdgeContains((EdgeContains) e);
			}
			else if (e instanceof EdgeEndsWith) {
				handleEdgeEndsWith((EdgeEndsWith) e);
			}
			else if (e instanceof EdgeIndexOf) {
				handleEdgeIndexOf((EdgeIndexOf) e);
			}
			else if (e instanceof EdgeIndexOfChar) {
				handleEdgeIndexOfChar((EdgeIndexOfChar) e);
			}
			else if (e instanceof EdgeLastIndexOfChar) {
				handleEdgeLastIndexOfChar((EdgeLastIndexOfChar) e);
			}
			else if (e instanceof EdgeLastIndexOfChar2) {
				handleEdgeLastIndexOfChar2((EdgeLastIndexOfChar2) e);
			}
			else if (e instanceof EdgeIndexOf2) {
				//println ("[isSat] EdgeIndexOf2");
				handleEdgeIndexOf2((EdgeIndexOf2) e);
			}
			else if (e instanceof EdgeIndexOfChar2) {
				//println ("[isSat] EdgeIndexOfChar2");
				handleEdgeIndexOfChar2((EdgeIndexOfChar2) e);
			}
			else if (e instanceof EdgeNotContains) {
				handleEdgeNotContains((EdgeNotContains) e);
			}
			else if (e instanceof EdgeNotEndsWith) {
				handleEdgeNotEndsWith((EdgeNotEndsWith) e);
			}
			else if (e instanceof EdgeSubstring1Equal) {
				handleEdgeSubstring1Equal((EdgeSubstring1Equal) e);
			}
			else if (e instanceof EdgeSubstring2Equal) {
				handleEdgeSubstring2Equal((EdgeSubstring2Equal) e);
			}
			else if (e instanceof EdgeReplaceCharChar) {
				handleEdgeReplaceCharChar((EdgeReplaceCharChar) e);
			}
			else {
				throw new RuntimeException("Edge not supported: " + e.getClass().toString());
			}
			if(expr != null) {
				//println ("[isSat] expr: " + expr.toString());
			}
		}
		//println ("[isSat] Done walking through the edges");
		/* TODO: Remove*/		
		if (expr == null) return true;
		//println(expr.toString());
		//vc.loadFile(fileName);
		vc.push();
		//long timing = System.currentTimeMillis();
		SatResult result = vc.checkUnsat(expr);
		//totalTiming += System.currentTimeMillis() - timing;
		if (result == SatResult.UNSATISFIABLE) {
			vc.pop();
			//println ("[isSat] Current solutions is unsat, extending lengts");
            LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
            for (Vertex v: g.getVertices()) {
            	if (!v.getName().startsWith("CHAR"))
            		loic.addToList(new LinearIntegerConstraint(v.getSymbolicLength(), Comparator.NE, new IntegerConstant(v.getSymbolicLength().solution())));
            }
            for (Edge e: g.getEdges()) {
            	if (e instanceof EdgeCharAt) {
            		EdgeCharAt eca = (EdgeCharAt) e;
            		loic.addToList(new LinearIntegerConstraint(eca.getIndex(), Comparator.NE, new IntegerConstant(eca.getIndex().solution())));
            		loic.addToList(new LinearIntegerConstraint(eca.getValue(), Comparator.NE, new IntegerConstant(eca.getValue().solution())));
            	}
            	else if (e instanceof EdgeIndexOf) {
            		EdgeIndexOf eio = (EdgeIndexOf) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
            	}
            	else if (e instanceof EdgeIndexOfChar) {
            		EdgeIndexOfChar eio = (EdgeIndexOfChar) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
            	}
            	else if (e instanceof EdgeLastIndexOfChar) {
            		EdgeLastIndexOfChar eio = (EdgeLastIndexOfChar) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
            	}
            	else if (e instanceof EdgeLastIndexOfChar2) {
            		EdgeLastIndexOfChar2 eio = (EdgeLastIndexOfChar2) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(eio.getIndex().getMinDist().solution())));
            	}
            	else if (e instanceof EdgeIndexOf2) {
            		EdgeIndexOf2 eio = (EdgeIndexOf2) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().getMinIndex().solution())));
            	}
            	else if (e instanceof EdgeIndexOfChar2) {
            		EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(eio.getIndex().getMinDist().solution())));
            	}
            	else if (e instanceof EdgeSubstring1Equal) {
            		EdgeSubstring1Equal es1e = (EdgeSubstring1Equal) e;
            		if (es1e.getArgument1Symbolic() != null) {
            			loic.addToList(new LinearIntegerConstraint(es1e.getArgument1Symbolic(), Comparator.NE, new IntegerConstant(es1e.getArgument1Symbolic().solution())));
            		}
            	}
            	else if (e instanceof EdgeSubstring2Equal) {
            		EdgeSubstring2Equal es2e = (EdgeSubstring2Equal) e;
            		if (es2e.getSymbolicArgument1() != null) {
            			loic.addToList(new LinearIntegerConstraint(es2e.getSymbolicArgument1(), Comparator.NE, new IntegerConstant(es2e.getSymbolicArgument1().solution())));
            		}
            		if (es2e.getSymbolicArgument2() != null) {
            			loic.addToList(new LinearIntegerConstraint(es2e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(es2e.getSymbolicArgument2().solution())));
            		}
            	}
            }
            //println ("[isSat] loic: " + loic);
            pc._addDet(loic);
            //println ("[isSat] firing up integer constraint solver");
            if (scg.isSatisfiable(pc)) {
            	//println ("[isSat] integer constriant solver found it to be sat, solving...");
				scg.solve(pc);
				pc.flagSolved = true;
				//println ("[isSat] solved PC: " + pc.header); 
				vc.delete();
				return isSat (g, pc); //TODO: Prevent infinite looping
			}
			else {
				//println ("[isSat] With the added constraint, could not be solved");
				vc.delete();
				return false;
			}
        }
        else if (result == SatResult.SATISFIABLE) {
        	HashMap model = vc.getConcreteModel();
        	//println(model.toString());
        	
        	for (Object e: model.entrySet()) {
        		Entry entry = (Entry) e;
        		String vertexName = entry.getKey().toString();
        		String rawData = entry.getValue().toString();
        		//println ("[rawData]: "+ rawData);
        		rawData = fromRawData(rawData);
        		////println (vertexName + " = " + rawData);
        		Vertex v = g.findVertex(vertexName);
        		v.setSolution(rawData);
        	}
        	
        	vc.pop();
        	vc.delete();
           // System.out.//println("Satisfiable (Invalid)\n");
            return true;
        }else{
        	vc.pop();
        	vc.delete();
        	return false;
        }
		
		//return true;
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
	
	private static Expr startsWith (Edge e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			ExprMut source = getExprMut (e.getSource());
			ExprMut dest = getExprMut (e.getDest());
			
			ExprMut temp = vc.newBVExtractExpr(source, e.getSource().getLength() * 8 - 1, (e.getSource().getLength() - e.getDest().getLength() + 1) * 8 - 8);
			return (vc.eqExpr(temp, dest));
			
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
			return (lit);
		}
		else if (!e.getDest().isConstant()) {
			//TODO Fix
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
			return (listOfLit);
		}
		else {
			String sourceConstant = e.getSource().getSolution();
			String destConstant = e.getDest().getSolution();
			//println ("[startsWith] sourceConstant: " + sourceConstant);
			//println ("[startsWith] destConstant: " + destConstant);
			
			if (sourceConstant.startsWith(destConstant)) {
				return vc.trueExpr();
			}
			else {
				return vc.falseExpr();
			}
		}
		//println ("[startsWith] returning null: " + e.toString());
		//return null;
	}
	
	private static void handleEdgeStartsWith (EdgeStartsWith e) {
		post (startsWith(e));
	}
	
	private static void handleEdgeNotStartsWith (EdgeNotStartsWith e) {
		if (e.getSource().getLength() < e.getDest().getLength()) return;
		post (vc.notExpr(startsWith(e)));
	}
	
	private static void handleEdgeReplaceCharChar (EdgeReplaceCharChar e) {
		ExprMut source = getExprMut (e.getSource());
		ExprMut dest = getExprMut (e.getDest());
		
		Expr setOflit = null;
		Expr lit;
		//println ("[handleEdgeReplaceCharChar] e.getSource().getLength(): " + e.getSource().getLength());
		for (int i = 1; i <= e.getSource().getLength(); i++) {
			lit = vc.iteExpr(vc.eqExpr(vc.newBVExtractExpr(source, i * 8 - 1, i * 8 - 8), vc.newBVConstExpr(toBits(e.getC1()))), 
					   vc.eqExpr(vc.newBVExtractExpr(dest, i * 8 - 1, i * 8 - 8), vc.newBVConstExpr(toBits(e.getC2()))),
					   vc.trueExpr());
			setOflit = and (setOflit, lit);
		}
		//println ("[handleEdgeReplaceCharChar] setOflit: " + setOflit);
		post (setOflit);
		
		setOflit = null;
		for (int i = 1; i <= e.getSource().getLength(); i++) {
			lit = vc.notExpr(vc.eqExpr(vc.newBVExtractExpr(dest, i * 8 - 1, i * 8 - 8), vc.newBVConstExpr(toBits(e.getC1()))));
			setOflit = and (setOflit, lit);
		}
		post (setOflit);
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
			//TODO:Fix
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
	
	private static void handleEdgeEndsWith (EdgeEndsWith e) {
		post (endsWith(e));
	}
	
	private static void handleEdgeNotEndsWith (EdgeNotEndsWith e) {
		if (e.getDest().getLength() > e.getSource().getLength()) {
			return;
		}
		post (vc.notExpr(endsWith(e)));
	}
	
	private static Expr equal (Edge e) {
		//println ("[equal] e: " + e.toString());
		if (e.getSource().getLength() != e.getDest().getLength()) {
			return vc.falseExpr();
		}
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
	
	
	private static void handleEdgeNotEqual (EdgeNotEqual e) {
		if (e.getSource().getLength() != e.getDest().getLength()) {
			return;
		}
		
		post (vc.notExpr(equal(e)));
	}
	
	private static void handleEdgeEqual (EdgeEqual e) {
		//println ("[handleEdgeEqual] entered: " + e.toString());
		post (equal(e));
	}
	
	private static void handleEdgeTrim (EdgeTrimEqual e) {
		//println ("[handleEdgeTrim] entered handleEdgeTrim " + e);
		if (e.getSource().getLength() == e.getDest().getLength()) {
			//println ("[handleEdgeTrim] 1. posting: " + equal(e));
			post (equal(e));
			return;
		}
		
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
			post (listOflit);
			
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
			//println ("[handleEdgeTrim] 3. posting: " + listOfLit);
			post (listOfLit);
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
			//println ("[handleEdgeTrim] 4. posting: " + lit);
			post (lit);
		}
	}
	
	public static void handleEdgeCharAt (EdgeCharAt e) {
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			char c = e.getValue().solutionChar();
			int index = e.getIndex().solutionInt();
			Expr temp = vc.newBVExtractExpr(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
			Expr cons = vc.newBVConstExpr(toBits(c));
			post (vc.eqExpr(temp, cons));
		}
		else {
			String constant = e.getSource().getSolution();
			char c = (char) e.getValue().solution();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				ExprMut temp1 = vc.newBVConstExpr(toBits(constant.charAt(index)));
				ExprMut temp2 = vc.newBVConstExpr(toBits(c));
				post (vc.eqExpr(temp1, temp2));
			}
			else {
				for (int i = 0; i < constant.length(); i++) {
					ExprMut temp1 = vc.newBVConstExpr(toBits(constant.charAt(i)));
					ExprMut temp2 = vc.newBVConstExpr(toBits(c));
					post (vc.notExpr(vc.eqExpr(temp1, temp2)));
				}
			}
		}
	}
	
	private static void handleEdgeConcat (EdgeConcat e) {
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
				post(lit);
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
				post (lit);
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
				post (lit);
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
				post(lit);
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
				post (lit);
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
				post (lit);
			}
		}
	}
	
	private static Expr contains (Edge e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			ExprMut dest = getExprMut(e.getDest());
			int diff = e.getSource().getLength() - e.getDest().getLength();
			Expr listOfLit = null;
			for (int i = 0; i <= diff; i++) {
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
			for (int i = 0; i <= diff; i++) {
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
			String[] possibleSolutions = new String [e.getSource().getLength() - e.getDest().getLength() + 1];
			for (int i = 0; i <= e.getSource().getLength() - e.getDest().getLength(); i++) {
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
	
	private static void handleEdgeContains (EdgeContains e) {
		if (e.getSource().getLength() == e.getDest().getLength()) {
			//println ("[handleEdgeContains] handing over to equals");
			post (equal(e));
			return;
		}
		post (contains(e));
	}
	
	private static void handleEdgeIndexOf2 (EdgeIndexOf2 e) {
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
				post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					post (vc.notExpr(equal(e)));
					return;
				}
				else {
					post (vc.notExpr(contains(e))); //TODO: fix this, it should take into account the minimal distance
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
				post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					post (vc.notExpr(equal(e)));
					return;
				}
				else {
					post (vc.notExpr(contains(e)));
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
				post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					post (vc.notExpr(equal(e)));
					return;
				}
				else {
					post (vc.notExpr(contains(e)));
				}
			}
		}
	}
	
	private static void handleEdgeIndexOf (EdgeIndexOf e) {
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
				post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					post (vc.notExpr(equal(e)));
					return;
				}
				else {
					post (vc.notExpr(contains(e)));
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
				post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					post (vc.notExpr(equal(e)));
					return;
				}
				else {
					post (vc.notExpr(contains(e)));
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
				post (lit);
			}
			else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				}
				else if (e.getSource().getLength() == e.getDest().getLength()) {
					post (vc.notExpr(equal(e)));
					return;
				}
				else {
					post (vc.notExpr(contains(e)));
				}
			}
		}
	}
	
	private static void handleEdgeIndexOfChar (EdgeIndexOfChar e) {
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
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
				post (lit);
				//println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			}
			else {
				Expr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				post (lit);
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.indexOf(character);
			post (vc.eqExpr(vc.ratExpr(actualAns), vc.ratExpr(index)));
		}
	}
	
	private static void handleEdgeLastIndexOfChar (EdgeLastIndexOfChar e) {
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
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
				post (lit);
				//println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			}
			else {
				Expr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				post (lit);
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.indexOf(character);
			post (vc.eqExpr(vc.ratExpr(actualAns), vc.ratExpr(index)));
		}
	}
	
	private static void handleEdgeLastIndexOfChar2 (EdgeLastIndexOfChar2 e) {
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				Expr lit = null;
				/* no other occurences of the character may come after up till second argument*/
				for (int i = index+1; i < e.getIndex().getMinDist().solution(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				Expr constant = vc.newBVConstExpr(toBits(character));
				lit = and (lit, vc.eqExpr(sourceTemp, constant));
				post (lit);
				//println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			}
			else {
				Expr lit = null;
				//Can not feature uptil the second argument
				for (int i = 0; i < e.getIndex().getMinDist().solution(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				post (lit);
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.lastIndexOf(character, e.getIndex().getMinDist().solutionInt());
			post (vc.eqExpr(vc.ratExpr(actualAns), vc.ratExpr(index)));
		}
	}
	
	private static void handleEdgeIndexOfChar2 (EdgeIndexOfChar2 e) {
		if (!e.getSource().isConstant()) {
			ExprMut source = getExprMut(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				//println ("[handleEdgeIndexOfChar2] branch 1");
				Expr lit = null;
				/* no other occurences of the character may come before */
				//println ("[handleEdgeIndexOfChar2] e.getIndex().getMinDist().solution() = " + e.getIndex().getMinDist().solution());
				int i = e.getIndex().getMinDist().solutionInt();
				if (e.getIndex().getMinDist().solution() < 0) {
					i = 0;
				}
				for (; i < index; i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - index) * 8 - 1, (e.getSource().getLength() - index) * 8 - 8);
				Expr constant = vc.newBVConstExpr(toBits(character));
				lit = and (lit, vc.eqExpr(sourceTemp, constant));
				post (lit);
			}
			else {
				Expr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - i) * 8 - 1, (e.getSource().getLength() - i) * 8 - 8);
					Expr constant = vc.newBVConstExpr(toBits(character));
					lit = and (lit, vc.notExpr(vc.eqExpr(sourceTemp, constant)));
				}
				post (lit);
			}
		}
		else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.indexOf(character, e.getIndex().getMinDist().solutionInt());
			post (vc.eqExpr(vc.ratExpr(actualAns), vc.ratExpr(index)));
		}
	}
	
	private static void handleEdgeNotContains (EdgeNotContains e) {
		if (e.getSource().getLength() < e.getDest().getLength()) {
			return;
		}
		post (vc.notExpr(contains(e)));
	}
	
	private static void handleEdgeSubstring1Equal (EdgeSubstring1Equal e) {
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
			post (lit);
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
			post (lit);
		}
		else {
			throw new RuntimeException("Preprocessor should handle this");
		}
	}
	
	private static void handleEdgeSubstring2Equal (EdgeSubstring2Equal e) {
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
				post (lit);
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
				post (lit);
			}
			else {
				throw new RuntimeException("Preprocessor should handle this");
			}
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
				post (lit);
			}
			else if (!e.getSource().isConstant()) {
				ExprMut source = getExprMut(e.getSource());
				String destCons = e.getDest().getSolution();
				int arg1 = e.getArgument1();
				int arg2 = e.getSymbolicArgument2().solutionInt();
				if (arg2 - arg1 != destCons.length()) {
					//TODO: Can definitly improve here
					//global_pc._addDet(Comparator.EQ, e.getSymbolicArgument2(), destCons.length() + arg1);
					post(vc.falseExpr());
					return;
					//throw new RuntimeException((arg2 - arg1) + " is not equal to '" + destCons + "' length of " + destCons.length());
				}
				Expr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					Expr sourceTemp = vc.newBVExtractExpr(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1, (e.getSource().getLength() - (i + arg1)) * 8 - 8);
					Expr destTemp = vc.newBVConstExpr(toBits(destCons.charAt(i)));
					lit = and (lit, vc.eqExpr(sourceTemp, destTemp));
				}
				post (lit);
			}
			else {
				throw new RuntimeException("Preprocessor should handle this");
			}
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
	
	private static void post (Expr e) {
		if (expr == null) {
			expr = e;
		}
		else {
			expr = vc.andExpr(e, expr);
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
	
}

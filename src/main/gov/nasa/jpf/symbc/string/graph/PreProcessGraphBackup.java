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

package gov.nasa.jpf.symbc.string.graph;

import java.util.ArrayList;
import java.util.List;

import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringUtility;
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;
import gov.nasa.jpf.util.LogManager;
import java.util.logging.Logger;

/**
 * This class does the preprocessing of the StringGraph
 */
public class PreProcessGraphBackup {
  static Logger logger = LogManager.getLogger("stringsolver");
	public static final int MAXIMUM_LENGTH = 30;
	private static SymbolicConstraintsGeneral scg;
	
	/**
	 * Preprocess given graph, and adds appropriate integer constraints to
	 * the pathcondition.
	 * 
	 * Returns false if the current graph is unsatisfiable.
	 * 
	 * @param g
	 * @param currentPC
	 * @return
	 */
	public static boolean preprocess (StringGraph g, PathCondition currentPC) { 
		//println ("[preprocess] Preprocessor running...");
		scg = new SymbolicConstraintsGeneral();
		
		/*if (!scg.isSatisfiable(currentPC)) {
			return false;
		}
		else {
			scg.solve(currentPC);
		}*/
		
		PathCondition pc = currentPC;
		
		//Remove duplicates
		List<Edge> temp = g.getEdges();
		for (int i = 0; i < temp.size(); i++) {
			for (int j = i + 1; j < temp.size(); j++) {
				if (temp.get(i).equals(temp.get(j))) {
					throw new RuntimeException("o oo " + temp.get(i).toString());
				}
			}
		}
		
		//Populate with equality and merge
		boolean change = true;
		while (change) { 
			change = false;
			Vertex v1, v2;
			for (int i = 0; i < g.getVertices().size(); i++) {
				for (int j = i+1; j < g.getVertices().size(); j++) {
					v1 = g.getVertices().get(i);
					v2 = g.getVertices().get(j);
					if (g.getEdges().contains(new EdgeEqual("", v1, v2))) {
						if (g.getEdges().contains(new EdgeNotEqual("", v1, v2))) {
							//println ("[preprocess] Two vertices have equality and non equality inbetween them");
							return false;
						}
						//println ("[preprocess] Merging " + v1.getName() + " and " + v2.getName());
						boolean mergeResult = g.mergeVertices (v1, v2);
						if (!mergeResult) {
							//println ("[preprocess] Merging returned unsat");
							return false;
						}
						//println(g.toDot());
						if (g.inconsistent()) {
							//println ("[preprocess] Inconsistent");
							return false;
						}
						change = true;
						/* Done merging, ensure both vertices lengths are the same */
						forceLengthsSame (v1, v2, pc);
					}
				}
			}
		}
		
		//Add equality between startswiths
		/*List<Edge> edgesToAdd = new ArrayList<Edge>();
		for (Edge e1: g.getEdges()) {
			for (Edge e2: g.getEdges()) {
				if (e1.equals(e2)) continue;
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!e1.getSource().equals(e2.getSource())) continue;
				if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeStartsWith) {
					Edge e = new EdgeEqual("SWEqual_" + e1.getDest().getName() + "_" + e2.getDest().getName(), e1.getDest(), e2.getDest());
					if (!edgesToAdd.contains(e)) edgesToAdd.add(e);
				}
			}
			
		}
		for (Edge e: edgesToAdd) {
			g.addEdge(e.getSource(), e.getDest(), e);
		}*/
		
		/*
		 * Populate with equality and merge, again, due to the previous
		 * step may have added equalities
		 */
		
		change = true;
		while (change) { 
			change = false;
			Vertex v1, v2;
			for (int i = 0; i < g.getVertices().size(); i++) {
				for (int j = i+1; j < g.getVertices().size(); j++) {
					v1 = g.getVertices().get(i);
					v2 = g.getVertices().get(j);
					if (g.getEdges().contains(new EdgeEqual("", v1, v2))) {
						if (g.getEdges().contains(new EdgeNotEqual("", v1, v2))) {
							//println ("[preprocess] Two vertices have equality and non equality inbetween them");
							return false;
						}
						//println ("[preprocess] Merging " + v1.getName() + " and " + v2.getName());
						boolean mergeResult = g.mergeVertices (v1, v2);
						if (!mergeResult) {
							//println ("[preprocess] Merging returned unsat");
							return false;
						}
						//println(g.toDot());
						if (g.inconsistent()) {
							//println ("[preprocess] Inconsistent");
							return false;
						}
						change = true;
						/* Done merging, ensure both vertices lengths are the same */
						forceLengthsSame (v1, v2, pc);
					}
				}
			}
		}
		
		//Remove unnecassery concat (a + b = c, where c is constant and a xor b is constant)
		for (Edge e: g.getEdges()) {
			if (e instanceof EdgeConcat) {
				if (e.getDest().isConstant()) {
					//println ("[preprocess] Entering concat constant handling");
					String destString = e.getDest().getSolution();
					if (e.getSources().get(0).isConstant() && e.getSources().get(1).isConstant()) {
						String leftString = e.getSources().get(0).getSolution();
						String rightString = e.getSources().get(1).getSolution();
						if (!leftString.concat(rightString).equals(destString)) {
							return false;
						}
					}
					else if (e.getSources().get(0).isConstant()) {
						String leftString = e.getSources().get(0).getSolution();
						if (!destString.startsWith(leftString)) {
							return false;
						}
						String rightPart = StringUtility.findRightSide(destString, leftString);
						e.getSources().get(1).setSolution(rightPart);
						e.getSources().get(1).setConstant(true);
						e.getSources().get(1).setLength(rightPart.length());
					}
					else if (e.getSources().get(1).isConstant()) {
						String rightString = e.getSources().get(1).getSolution();
						if (!destString.endsWith(rightString)) {
							return false;
						}
						String leftPart = StringUtility.findLeftSide(destString, rightString);
						e.getSources().get(0).setSolution(leftPart);
						e.getSources().get(0).setConstant(true);
						e.getSources().get(0).setLength(leftPart.length());
					}
				}
				else {
					if (e.getSources().get(0).isConstant() && e.getSources().get(1).isConstant() && !e.getDest().isConstant()) {
						String leftString = e.getSources().get(0).getSolution();
						String rightString = e.getSources().get(1).getSolution();
						String concatString = leftString.concat(rightString);
						e.getDest().setSolution(concatString);
						e.getDest().setConstant(true);
						e.getDest().setLength(concatString.length());
					}
				}
			}
		}
		
		//Sort out complicated charAt and startswith/endswith
		for (Edge e1: g.getEdges()) {
			for (Edge e2: g.getEdges()) {
				if (e1.equals(e2)) continue;
				if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeCharAt 
					&& e1.getSource().equals(e2.getSource()) && e1.getDest().isConstant()) {
					EdgeCharAt eca = (EdgeCharAt) e2;
					if (eca.getIndex() instanceof IntegerConstant && eca.getValue() instanceof IntegerConstant 
							&& eca.getIndex().solution() < e1.getDest().getSolution().length()) {
							String startsWithString = e1.getDest().getSolution();
							int charAtIndex = (int) eca.getIndex().solution();
							if (startsWithString.charAt(charAtIndex) != charAtIndex) {
								return false;
							}
					}
				}
				//Can't say anything about endswith
			}
		}
		
		
		
		//Concrete startswith/endswith/substring, necassery for charAt.
		for (Edge e1: g.getEdges()) {
			for (Edge e2: g.getEdges()) {
				if (e1.equals(e2)) continue;
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!e1.getSource().equals(e2.getSource())) continue;
				if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeCharAt) {
					if (e1.getDest().isConstant()) {
						EdgeCharAt eca = (EdgeCharAt) e2;
						String solution = e1.getDest().getSolution();
						for (int i = 0; i < solution.length(); i++) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.NE, new IntegerConstant(i)));
							loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(solution.charAt(i))));
							pc._addDet(loic);
						}
					}
				}
				else if (e1 instanceof EdgeEndsWith && e2 instanceof EdgeCharAt) {
					if (e1.getDest().isConstant()) {
						EdgeCharAt eca = (EdgeCharAt) e2;
						String solution = e1.getDest().getSolution();
						for (int i = 0; i < solution.length(); i++) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.NE, e1.getSource().getSymbolicLength()._minus(solution.length() - i)));
							loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(solution.charAt(i))));
							pc._addDet(loic);
						}
					}
				}
				else if (e1 instanceof EdgeSubstring1Equal && e2 instanceof EdgeCharAt) {
					if (e1.getDest().isConstant()) {
						EdgeCharAt eca = (EdgeCharAt) e2;
						EdgeSubstring1Equal es1e = (EdgeSubstring1Equal) e1;
						String solution = e1.getDest().getSolution();
						for (int i = 0; i < solution.length(); i++) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.NE, new IntegerConstant(es1e.getArgument1() + i)));
							loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(solution.charAt(i))));
							pc._addDet(loic);
						}
					}
				}
				else if (e1 instanceof EdgeSubstring2Equal && e2 instanceof EdgeCharAt) {
					if (e1.getDest().isConstant()) {
						EdgeCharAt eca = (EdgeCharAt) e2;
						EdgeSubstring2Equal es2e = (EdgeSubstring2Equal) e1;
						String solution = e1.getDest().getSolution();
						for (int i = 0; i < solution.length(); i++) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.NE, new IntegerConstant(es2e.getArgument1() + i)));
							loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(solution.charAt(i))));
							pc._addDet(loic);
						}
					}
				}
			}
		}
		
		//Concrete startswith, endswith, substring and charAt for indexOf (needs update for the newer indexOf constraints)
		for (Edge e1: g.getEdges()) {
			for (Edge e2: g.getEdges()) {
				if (e1.equals(e2)) continue;
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!e1.getSource().equals(e2.getSource())) continue;
				if (PathCondition.flagSolved == false && scg.isSatisfiable(pc)) {
					scg.solve(pc);
					PathCondition.flagSolved = true;
				}
				else if (PathCondition.flagSolved == false){
					//println ("[preprocess] Intermediate solving failed");
					return false;
				}
				if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeIndexOf) {
					EdgeIndexOf eio = (EdgeIndexOf) e2;
					if (eio.getIndex().getExpression() instanceof StringConstant && e1.getDest().isConstant()) {
						int possiblePos = e1.getDest().getSolution().indexOf(eio.getIndex().getExpression().solution());
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						int lengthOfExpression = eio.getIndex().getExpression().solution().length();
						/* a.sw(c).indexOf(b) == j
						 * a.indexof(b) == i
						 * 
						 * assume b is constant
						 * 
						 * 0 < i < c.length -> i == j  
						 */
						loic.addToList(new LinearIntegerConstraint(new IntegerConstant(0), Comparator.GT, eio.getIndex()));
						loic.addToList(new LinearIntegerConstraint( eio.getIndex(), Comparator.GT, new IntegerConstant(lengthOfExpression)));
						loic.addToList(new LinearIntegerConstraint( eio.getIndex(), Comparator.EQ, new IntegerConstant (possiblePos)));
						if (!pc.hasConstraint(loic)) pc._addDet(loic);
						pc._addDet(Comparator.GE, eio.getIndex(), new IntegerConstant(possiblePos));
					}
				}
				else if (e1 instanceof EdgeEndsWith && e2 instanceof EdgeIndexOf) {
					// TODO: Rethink about the fact that indexOf returns the first occurence
					EdgeIndexOf eio = (EdgeIndexOf) e2;
					if (eio.getIndex().getExpression() instanceof StringConstant && e1.getDest().isConstant()) {
						int possiblePos = e1.getDest().getSolution().indexOf(eio.getIndex().getExpression().solution());
						int lastPossiblePos = e1.getDest().getSolution().lastIndexOf(eio.getIndex().getExpression().solution());
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						int lengthOfExpression = eio.getIndex().getExpression().solution().length();
						/* a.sw(c).indexOf(b) == j
						 * a.indexof(b) == i
						 * 
						 * assume b is constant
						 * 
						 * 0 < i < c.length -> i == j  
						 */
						loic.addToList(new LinearIntegerConstraint(e1.getSource().getSymbolicLength()._minus(lengthOfExpression), Comparator.GE, eio.getIndex()));
						loic.addToList(new LinearIntegerConstraint( eio.getIndex(), Comparator.GE, e1.getSource().getSymbolicLength()));
						loic.addToList(new LinearIntegerConstraint( eio.getIndex(), Comparator.EQ, e1.getSource().getSymbolicLength()._minus(lengthOfExpression)._plus(new IntegerConstant (possiblePos))));
						pc._addDet(loic);
						pc._addDet(Comparator.LE, eio.getIndex(), e1.getSource().getSymbolicLength()._minus(lengthOfExpression - lastPossiblePos));
					}
				}
				else if (e1 instanceof EdgeSubstring1Equal && e2 instanceof EdgeIndexOf) {
					EdgeIndexOf eio = (EdgeIndexOf) e2;
					EdgeSubstring1Equal es1e = (EdgeSubstring1Equal) e1;
					if (eio.getIndex().getExpression() instanceof StringConstant && e1.getDest().isConstant()) {
						int possiblePos = e1.getDest().getSolution().indexOf(eio.getIndex().getExpression().solution());
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						/* a.sw(c).indexOf(b) == j
						 * a.indexof(b) == i
						 * 
						 * assume b is constant
						 * 
						 * 0 < i < c.length -> i == j  
						 */
						loic.addToList(new LinearIntegerConstraint(new IntegerConstant(es1e.a1), Comparator.GE, eio.getIndex()));
						loic.addToList(new LinearIntegerConstraint( eio.getIndex(), Comparator.GE, new IntegerConstant(es1e.a1)._plus(e2.getDest().getSymbolicLength())));
						loic.addToList(new LinearIntegerConstraint( eio.getIndex(), Comparator.EQ, new IntegerConstant(es1e.a1)._plus(new IntegerConstant (possiblePos))));
						pc._addDet(loic);
					}
				}
				else if (e1 instanceof EdgeSubstring2Equal && e2 instanceof EdgeIndexOf) {
					EdgeIndexOf eio = (EdgeIndexOf) e2;
					EdgeSubstring2Equal es2e = (EdgeSubstring2Equal) e1;
					if (eio.getIndex().getExpression() instanceof StringConstant && e1.getDest().isConstant()) {
						int possiblePos = e1.getDest().getSolution().indexOf(eio.getIndex().getExpression().solution());
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						/* a.sw(c).indexOf(b) == j
						 * a.indexof(b) == i
						 * 
						 * assume b is constant
						 * 
						 * 0 < i < c.length -> i == j  
						 */
						loic.addToList(new LinearIntegerConstraint(new IntegerConstant(es2e.getArgument1()), Comparator.GE, eio.getIndex()));
						loic.addToList(new LinearIntegerConstraint( eio.getIndex(), Comparator.GE, new IntegerConstant(es2e.getArgument2())));
						loic.addToList(new LinearIntegerConstraint( eio.getIndex(), Comparator.EQ, new IntegerConstant(es2e.getArgument1())._plus(new IntegerConstant (possiblePos))));
						pc._addDet(loic);
					}
				}
				else if (e1 instanceof EdgeCharAt && e2 instanceof EdgeIndexOf) {
					//println ("[preprocess] Path followed 1");
					EdgeIndexOf eio = (EdgeIndexOf) e2;
					EdgeCharAt eca = (EdgeCharAt) e1;
					StringExpression se = eio.getIndex().getExpression();
					if (se instanceof StringConstant) {
						//println ("[preprocess] Path followed 2");
						//TODO: This seems wrong
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) se.solution().charAt(0)), Comparator.EQ, eca.getValue()) );
						loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, eca.getIndex()));
						if (!pc.hasConstraint(loic)) pc._addDet(loic);
					}
				}
				else if (e1 instanceof EdgeCharAt && e2 instanceof EdgeIndexOf2) {
					//println ("[preprocess] Path followed 1");
					EdgeIndexOf2 eio = (EdgeIndexOf2) e2;
					EdgeCharAt eca = (EdgeCharAt) e1;
					StringExpression se = eio.getIndex().getExpression();
					if (se instanceof StringConstant) {
						//println ("[preprocess] Path followed 2");
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) se.solution().charAt(0)), Comparator.EQ, eca.getValue()) );
						loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, eca.getIndex()));
						loic.comment = "indexOfStrInt and charAt";
						if (!pc.hasConstraint(loic)) pc._addDet(loic);
					}
				}
				else if (e1 instanceof EdgeCharAt && e2 instanceof EdgeIndexOfChar) {
					EdgeIndexOfChar eio = (EdgeIndexOfChar) e2;
					EdgeCharAt eca = (EdgeCharAt) e1;
					IntegerExpression se = eio.getIndex().getExpression();
					if (se instanceof IntegerConstant) {
						//println ("[preprocess] Path followed 2");
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(se, Comparator.EQ, eca.getValue()) );
						loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, eca.getIndex()));
						if (!pc.hasConstraint(loic)) pc._addDet(loic);
					}
				}
				else if (e1 instanceof EdgeCharAt && e2 instanceof EdgeIndexOfChar2) {
					EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e2;
					EdgeCharAt eca = (EdgeCharAt) e1;
					IntegerExpression se = eio.getIndex().getExpression();
					if (se instanceof IntegerConstant) {
						//println ("[preprocess] Path followed 2");
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(se, Comparator.EQ, eca.getValue()) );
						loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, eca.getIndex()));
						loic.comment = "charAt and indexOfCharInt";
						if (!pc.hasConstraint(loic)) pc._addDet(loic);
					}
				}
				else if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeLastIndexOfChar) {
					EdgeStartsWith esw = (EdgeStartsWith) e1;
					EdgeLastIndexOfChar elio = (EdgeLastIndexOfChar) e2;
					IntegerExpression ie = elio.getIndex().getExpression();
					if (esw.getDest().isConstant() && ie instanceof IntegerConstant) {
						String startsWith = esw.getDest().getSolution();
						char character = (char) ie.solution();
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						if (startsWith.lastIndexOf(character) == -1) {
							loic.addToList(new LinearIntegerConstraint(elio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
							loic.addToList(new LinearIntegerConstraint(elio.getIndex(), Comparator.GE, new IntegerConstant(startsWith.length())));
						}
						else {
							loic.addToList(new LinearIntegerConstraint(elio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
							loic.addToList(new LinearIntegerConstraint(elio.getIndex(), Comparator.GE, new IntegerConstant(startsWith.lastIndexOf(character))));
						}
						if (!pc.hasConstraint(loic)) pc._addDet(loic);
					}
				}
			}
		}
		
		//TODO: Remove
		int stupidCount = 0;
		
		//Speedup dependencies between indexOf's, TODO: There's more to add
		for (Edge e1: g.getEdges()) {
			for (Edge e2: g.getEdges()) {
				if (e1.equals(e2)) continue;
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!e1.getSource().equals(e2.getSource())) continue;
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeIndexOfChar) {
					EdgeIndexOf eio = (EdgeIndexOf) e1;
					EdgeIndexOfChar eioc = (EdgeIndexOfChar) e2;
					if (eio.getIndex().getExpression() instanceof StringConstant) {
						String constant = eio.getIndex().getExpression().solution();
						for (int i = 0; i < constant.length(); i++) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant.charAt(i)), Comparator.EQ, eioc.getIndex().getExpression()));
							loic.addToList(new LinearIntegerConstraint(eio.getIndex()._plus(i), Comparator.NE, eioc.getIndex()));
							if (!pc.hasConstraint(loic)) pc._addDet(loic);
						}
					}
				}
				else if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeIndexOfChar2) {
					EdgeIndexOf2 eio = (EdgeIndexOf2) e1;
					EdgeIndexOfChar2 eioc = (EdgeIndexOfChar2) e2;
					if (eio.getIndex().getExpression() instanceof StringConstant) {
						String constant = eio.getIndex().getExpression().solution();
						for (int i = 0; i < constant.length(); i++) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant.charAt(i)), Comparator.EQ, eioc.getIndex().getExpression()));
							loic.addToList(new LinearIntegerConstraint(eio.getIndex()._plus(i), Comparator.NE, eioc.getIndex()));
							loic.comment = "indexOfStrInt and indexOfCharInt";
							if (!pc.hasConstraint(loic)) pc._addDet(loic);
						}
					}
				}
				else if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeIndexOfChar) {
					EdgeIndexOf2 eio = (EdgeIndexOf2) e1;
					EdgeIndexOfChar eioc = (EdgeIndexOfChar) e2;
					if (eio.getIndex().getExpression() instanceof StringConstant) {
						String constant = eio.getIndex().getExpression().solution();
						for (int i = 0; i < constant.length(); i++) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant.charAt(i)), Comparator.EQ, eioc.getIndex().getExpression()));
							loic.addToList(new LinearIntegerConstraint(eio.getIndex()._plus(i), Comparator.NE, eioc.getIndex()));
							loic.comment = "indexOfStrInt and indexOfCharInt";
							if (!pc.hasConstraint(loic)) pc._addDet(loic);
						}
					}
				}
				else if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeIndexOfChar2) {
					EdgeIndexOf eio = (EdgeIndexOf) e1;
					EdgeIndexOfChar2 eioc = (EdgeIndexOfChar2) e2;
					if (eio.getIndex().getExpression() instanceof StringConstant) {
						String constant = eio.getIndex().getExpression().solution();
						for (int i = 0; i < constant.length(); i++) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant.charAt(i)), Comparator.EQ, eioc.getIndex().getExpression()));
							loic.addToList(new LinearIntegerConstraint(eio.getIndex()._plus(i), Comparator.NE, eioc.getIndex()));
							if (!pc.hasConstraint(loic)) pc._addDet(loic);
						}
					}
				}
				else if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeIndexOf2) {
					EdgeIndexOf2 eio1 = (EdgeIndexOf2) e1;
					EdgeIndexOf2 eio2 = (EdgeIndexOf2) e2;
					if (eio1.getIndex().getExpression() instanceof StringConstant && eio2.getIndex().getExpression() instanceof StringConstant) {
						String constant1 = eio1.getIndex().getExpression().solution();
						String constant2 = eio2.getIndex().getExpression().solution();
						stupidCount ++;
						for (int i = 0; i < constant1.length(); i++) {
							for (int j = i; j < constant2.length(); j++) {
								if (constant1.charAt(i) != constant2.charAt(j)) {
									LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
									loic.addToList(new LinearIntegerConstraint(eio1.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
									loic.addToList(new LinearIntegerConstraint(eio2.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
									loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(i), Comparator.NE, eio2.getIndex()._plus(j)));
									loic.comment = "indexOfStrInt and indexOfStrInt " + stupidCount;
									pc._addDet(loic);
									//pc._addDet(Comparator.NE, eio1.getIndex()._plus(i), eio2.getIndex()._plus(j));
								}
							}
						}
					}
				}
				else if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeIndexOf) {
					EdgeIndexOf eio1 = (EdgeIndexOf) e1;
					EdgeIndexOf eio2 = (EdgeIndexOf) e2;
					if (eio1.getIndex().getExpression() instanceof StringConstant && eio2.getIndex().getExpression() instanceof StringConstant) {
						String constant1 = eio1.getIndex().getExpression().solution();
						String constant2 = eio2.getIndex().getExpression().solution();
						for (int i = 0; i < constant1.length(); i++) {
							for (int j = i; j < constant2.length(); j++) {
								if (constant1.charAt(i) != constant2.charAt(j)) {
									LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
									loic.addToList(new LinearIntegerConstraint(eio1.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
									loic.addToList(new LinearIntegerConstraint(eio2.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
									loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(i), Comparator.NE, eio2.getIndex()._plus(j)));
									pc._addDet(loic);
								}
							}
						}
					}
				}
				else if (e1 instanceof EdgeIndexOfChar && e2 instanceof EdgeIndexOfChar2) {
					EdgeIndexOfChar eioc = (EdgeIndexOfChar) e1;
					EdgeIndexOfChar2 eioc2 = (EdgeIndexOfChar2) e2;
					if (eioc.getIndex().getExpression() instanceof IntegerConstant && eioc2.getIndex().getExpression() instanceof IntegerConstant) {
						int sol1 = (int) eioc.getIndex().getExpression().solution();
						int sol2 = (int) eioc2.getIndex().getExpression().solution();
						if (sol1 != sol2) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
							loic.addToList(new LinearIntegerConstraint(eioc2.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
							loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, eioc2.getIndex()));
							pc._addDet(loic);
						}
					}
				}
			}
		}
		
		
		
		//Speedup between charAt and indexOf
		for (Edge e1: g.getEdges()) {
			for (Edge e2: g.getEdges()) {
				if (PathCondition.flagSolved == false && scg.isSatisfiable(pc)) {
					scg.solve(pc);
					PathCondition.flagSolved = true;
				}
				else if (PathCondition.flagSolved == false){
					//println ("[preprocess] Intermediate solving failed");
					return false;
				}
				if (e1.equals(e2)) continue;
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!e1.getSource().equals(e2.getSource())) continue;
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeCharAt) {
					EdgeIndexOf eio = (EdgeIndexOf) e1;
					EdgeCharAt eca = (EdgeCharAt) e2;
					if (e1.getDest().isConstant()) {
						String solution = e1.getDest().getSolution();
						char character = (char) eca.getValue().solution();
						int indexOf = solution.indexOf(String.valueOf(character));
						if (indexOf > -1) {
							//throw new RuntimeException("reached");
							pc._addDet(Comparator.NE,eio.getIndex(), new IntegerConstant(-1));
						}
						
					}
				}
				else if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeCharAt) {
					EdgeIndexOf2 eio = (EdgeIndexOf2) e1;
					EdgeCharAt eca = (EdgeCharAt) e2;
					if (e1.getDest().isConstant()) {
						String solution = e1.getDest().getSolution();
						char character = (char) eca.getValue().solution();
						int indexOf = solution.indexOf(String.valueOf(character));
						if (indexOf > -1) {
							//throw new RuntimeException("reached");
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(eca.getIndex(), Comparator.LT, eio.getIndex().getMinIndex()));
							loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE,new IntegerConstant(-1)));
							loic.comment = "indexOfStrInt and charAt";
							pc._addDet(loic);
						}
						
					}
				}
				else if (e1 instanceof EdgeIndexOfChar && e2 instanceof EdgeCharAt) {
					EdgeIndexOfChar eio = (EdgeIndexOfChar) e1;
					EdgeCharAt eca = (EdgeCharAt) e2;
					if (e1.getDest().isConstant()) {
						String solution = e1.getDest().getSolution();
						char character = (char) eca.getValue().solution();
						int indexOf = solution.indexOf(String.valueOf(character));
						if (indexOf > -1) {
							//throw new RuntimeException("reached");
							pc._addDet(Comparator.NE,eio.getIndex(), new IntegerConstant(-1));
						}
						
					}
				}
				else if (e1 instanceof EdgeIndexOfChar2 && e2 instanceof EdgeCharAt) {
					EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e1;
					EdgeCharAt eca = (EdgeCharAt) e2;
					if (e1.getDest().isConstant()) {
						String solution = e1.getDest().getSolution();
						char character = (char) eca.getValue().solution();
						int indexOf = solution.indexOf(String.valueOf(character));
						if (indexOf> -1) {
							LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
							loic.addToList(new LinearIntegerConstraint(eca.getIndex(), Comparator.LT, eio.getIndex().getMinDist()));
							loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE,new IntegerConstant(-1)));
							loic.comment = "indexOfCharInt and charAt";
							pc._addDet(loic);
						}
						
					}
				}
			}
		}
		
		/*Speedup replace (big speedup)*/
		for (Edge e1: g.getEdges()) {
			for (Edge e2: g.getEdges()) {
				if (e1.equals(e2)) continue;
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!e1.getSource().equals(e2.getDest())) continue;
				if (e1 instanceof EdgeContains && e2 instanceof EdgeReplaceCharChar) {
					
					EdgeContains ec = (EdgeContains) e1;
					if (ec.getDest().isConstant()) {
						String containsString = ec.getDest().getSolution();
						EdgeReplaceCharChar ercc = (EdgeReplaceCharChar) e2;
						char noMoreChar = ercc.getC1();
						if (containsString.contains(String.valueOf(noMoreChar))) {
							return false;
						}
					}
				}
			}
		}
		
		//Determine size of vertecis
		change = true;
		
		for (Vertex v: g.getVertices()) {
			pc._addDet(Comparator.GE, v.getSymbolicLength(), 1);
			pc._addDet(Comparator.LE, v.getSymbolicLength(), MAXIMUM_LENGTH);
		}
		//println ("amper klaar");
		//println (g.toDot());
		//println (currentPC.header.toString());
		while (change) {
			change = false;
			for (Edge e: g.getEdges()) {
				
				//println ("Edge: " + e);
				if (e.allVertecisAreConstant()) {
					//println ("all constants");
					//Should handle all constants here
					if (e instanceof EdgeContains) {
						if (!e.getSource().getSolution().contains(e.getDest().getSolution())) {
							return false;
						}
					}
					else if (e instanceof EdgeNotContains) {
						if (e.getSource().getSolution().contains(e.getDest().getSolution())) {
							return false;
						}
					}
					else if (e instanceof EdgeEndsWith) {
						if (!e.getSource().getSolution().endsWith(e.getDest().getSolution())) {
							return false;
						}
					}
					else if (e instanceof EdgeNotEndsWith) {
						if (e.getSource().getSolution().endsWith(e.getDest().getSolution())) {
							return false;
						}
					}
					else if (e instanceof EdgeStartsWith) {
						if (!e.getSource().getSolution().startsWith(e.getDest().getSolution())) {
							return false;
						}
					}
					else if (e instanceof EdgeNotStartsWith) {
						if (e.getSource().getSolution().startsWith(e.getDest().getSolution())) {
							return false;
						}
					}
					else if (e instanceof EdgeEqual) {
						if (!e.getSource().getSolution().equals(e.getDest().getSolution())) {
							return false;
						}
					}
					else if (e instanceof EdgeNotEqual) {
						if (e.getSource().getSolution().equals(e.getDest().getSolution())) {
							return false;
						}
					}
					else if (e instanceof EdgeSubstring1Equal) {
						EdgeSubstring1Equal es1e = (EdgeSubstring1Equal) e;
						if (e.getDest().getSolution().length() + es1e.getArgument1() > e.getSource().getSolution().length()) {
							return false;
						}
						if (!e.getSource().getSolution().substring(es1e.getArgument1()).equals((e.getDest().getSolution()))) {
							return false;
						}
					}
					else if (e instanceof EdgeSubstring2Equal) {
						EdgeSubstring2Equal es2e = (EdgeSubstring2Equal) e;
						if (es2e.getSymbolicArgument2() == null && !e.getSource().getSolution().substring(es2e.getArgument1(),es2e.getArgument2()).equals((e.getDest().getSolution()))) {
							return false;
						}
					}
					else if (e instanceof EdgeIndexOf) {
						EdgeIndexOf eio = (EdgeIndexOf) e;
						int indexOf = eio.getSource().getSolution().indexOf(eio.getDest().getSolution());
						pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(indexOf));
					}
					else if (e instanceof EdgeIndexOf2) {
						EdgeIndexOf2 eio = (EdgeIndexOf2) e;
						int indexOf = eio.getSource().getSolution().indexOf(eio.getDest().getSolution());
						if (indexOf == -1) {
							pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(-1));
						}
					}
					continue;
				}
				
				
				if (e instanceof EdgeEqual) {
					pc._addDet(Comparator.EQ, e.getSource().getSymbolicLength(), e.getDest().getSymbolicLength());
				}
				else if (e instanceof EdgeEndsWith) {
					//println ("EdgeEndsWith here");
					pc._addDet (Comparator.LE, e.getDest().getSymbolicLength(), e.getSource().getSymbolicLength());
				}
				else if (e instanceof EdgeStartsWith) {
					pc._addDet (Comparator.LE, e.getDest().getSymbolicLength(), e.getSource().getSymbolicLength());
				}
				else if (e instanceof EdgeSubstring1Equal) {
					EdgeSubstring1Equal es1e = (EdgeSubstring1Equal) e;
					pc._addDet (Comparator.LE, e.getDest().getSymbolicLength(), e.getSource().getSymbolicLength());
					pc._addDet(Comparator.GE, e.getSource().getSymbolicLength(), new IntegerConstant(es1e.a1)._plus(e.getDest().getSymbolicLength()));
					if (es1e.getArgument1Symbolic() != null) {
						pc._addDet(Comparator.GE, es1e.getArgument1Symbolic(), 0);
					}
				}
				else if (e instanceof EdgeSubstring2Equal) {
					EdgeSubstring2Equal es2e = (EdgeSubstring2Equal) e;
					if (!es2e.hasSymbolicArgs()) {
						pc._addDet (Comparator.LE, e.getDest().getSymbolicLength(), e.getSource().getSymbolicLength());
						pc._addDet (Comparator.GE, e.getSource().getSymbolicLength(), new IntegerConstant(es2e.getArgument2()));
						pc._addDet(Comparator.EQ, e.getDest().getSymbolicLength(), new IntegerConstant(es2e.getArgument2() - es2e.getArgument1()));
					}
					else if (es2e.getSymbolicArgument1() == null && es2e.getSymbolicArgument2() != null){
						pc._addDet (Comparator.LE, e.getDest().getSymbolicLength(), e.getSource().getSymbolicLength());
						pc._addDet (Comparator.GE, e.getSource().getSymbolicLength(), es2e.getSymbolicArgument2());
						pc._addDet (Comparator.GE, es2e.getSymbolicArgument2(), 0);
						pc._addDet (Comparator.GE, es2e.getSymbolicArgument2(), es2e.getArgument1());
						//pc._addDet(Comparator.EQ, e.getDest().getSymbolicLength(), new IntegerConstant(es2e.a2 - es2e.a1));
					}
					else {
						throw new RuntimeException ("Not supported, yet");
					}
				}
				else if (e instanceof EdgeTrimEqual) {
					pc._addDet (Comparator.LE, e.getDest().getSymbolicLength(), e.getSource().getSymbolicLength());
					//Fix a stupid bug in Trim of JSA
					pc._addDet (Comparator.GE, e.getDest().getSymbolicLength(), new IntegerConstant(2));
				}
				else if (e instanceof EdgeConcat) {
					/*if (e.getSources().get(0).isConstant() && e.getSources().get(1).isConstant() && e.getDest().isConstant()) {
						if (!e.getSources().get(0).getSolution().concat(e.getSources().get(1).getSolution()).equals(e.getDest().getSolution())) {
							return false;
						}
					}*/
					pc._addDet (Comparator.EQ, e.getSources().get(0).getSymbolicLength()._plus(e.getSources().get(1).getSymbolicLength()), e.getDest().getSymbolicLength());
				}
				else if (e instanceof EdgeIndexOf) {
					EdgeIndexOf eio = (EdgeIndexOf) e;
					/* Caused huge performance drop, not anymore, was due to orring with temp vars with rang 0, max */
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.GE, eio.getIndex()._plus(e.getDest().getSymbolicLength())));
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
				else if (e instanceof EdgeLastIndexOf) {
					EdgeLastIndexOf eio = (EdgeLastIndexOf) e;
					/* Caused huge performance drop, not anymore, was due to orring with temp vars with rang 0, max */
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.GE, eio.getIndex()._plus(e.getDest().getSymbolicLength())));
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
				else if (e instanceof EdgeIndexOfChar) {
					EdgeIndexOfChar eio = (EdgeIndexOfChar) e;
					/* Caused huge performance drop, not anymore, was due to orring with temp vars with rang 0, max */
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.GT, eio.getIndex()));
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
				else if (e instanceof EdgeLastIndexOfChar) {
					EdgeLastIndexOfChar eio = (EdgeLastIndexOfChar) e;
					/* Caused huge performance drop, not anymore, was due to orring with temp vars with rang 0, max */
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.GT, eio.getIndex()));
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
				else if (e instanceof EdgeIndexOf2) {
					EdgeIndexOf2 eio = (EdgeIndexOf2) e;
					/* Caused huge performance drop, not anymore, was due to orring with temp vars with rang 0, max */
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.GE, eio.getIndex()._plus(e.getDest().getSymbolicLength())));
					loic.comment = "indexOfStrInt basic 1";
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
					loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.GE, eio.getIndex().getMinIndex()));
					loic.comment = "indexOfStrInt basic 2";
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
				else if (e instanceof EdgeLastIndexOf2) {
					EdgeLastIndexOf2 eio = (EdgeLastIndexOf2) e;
					/* Caused huge performance drop, not anymore, was due to orring with temp vars with rang 0, max */
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.GE, eio.getIndex()._plus(e.getDest().getSymbolicLength())));
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
					loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.LE, eio.getIndex().getMinIndex()));
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
				else if (e instanceof EdgeIndexOfChar2) {
					EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e;
					/* Caused huge performance drop, not anymore, was due to orring with temp vars with rang 0, max */
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.GT, eio.getIndex()));
					loic.comment = "indexOfCharInt basic part 1";
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
					loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.GE, eio.getIndex().getMinDist()));
					loic.comment = "indexOfCharInt basic part 2";
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
				else if (e instanceof EdgeLastIndexOfChar2) {
					EdgeLastIndexOfChar2 eio = (EdgeLastIndexOfChar2) e;
					/* Caused huge performance drop, not anymore, was due to orring with temp vars with rang 0, max */
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.GT, eio.getIndex()));
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
					loic = new LogicalORLinearIntegerConstraints();
					loic.addToList (new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.LE, eio.getIndex().getMinDist()));
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
				else if (e instanceof EdgeCharAt) {
					EdgeCharAt eca = (EdgeCharAt) e;
					pc._addDet(Comparator.GT, e.getSource().getSymbolicLength(), eca.index);
					pc._addDet(Comparator.GE, eca.index, 0);
					pc._addDet(Comparator.LT, eca.index, MAXIMUM_LENGTH);
					pc._addDet(Comparator.GE, eca.value, SymbolicStringConstraintsGeneral.MIN_CHAR);
					pc._addDet(Comparator.LT, eca.value, SymbolicStringConstraintsGeneral.MAX_CHAR);
				}
				else if (e instanceof EdgeContains) {
					//println ("Here");
					pc._addDet(Comparator.GE, e.getSource().getSymbolicLength(), e.getDest().getSymbolicLength());
				}
				else if (e instanceof EdgeReplaceCharChar) {
					pc._addDet(Comparator.EQ, e.getSource().getSymbolicLength(), e.getDest().getSymbolicLength());
				}
				
				
			}
		}
		//println ("Done with loop");
		
		if (scg.isSatisfiable(pc)) { 
			//println ("is Sat");
			scg.solve(pc);
			PathCondition.flagSolved = true;
			System.out.println("HIERSO");
			for (Vertex v: g.getVertices()) {
				System.out.println(v.getName() + " " + v.getSymbolicLength().solution());
			}
			if (pc.header != null) {
				//println(pc.header.toString());
			}
		}
		else {
			//println ("[preprocess] Some constraints could not be resolved");
			//println(pc.header.toString());
			/*pc.header = pc.header.and;
			while (!scg.isSatisfiable(pc) && pc.header != null) {
				pc.header = pc.header.and;
			}
			if (scg.isSatisfiable(pc)) {
				//println ("[preprocess] This was last sat:");
				
				//println ("is Sat");
				scg.solve(pc);
				PathCondition.flagSolved = true;
				if (pc.header != null) {
					//println(pc.header.toString());
				}
				for (Vertex v: g.getVertices()) {
					if (v.getName().equals("str_1_SYMSTRING")) {
						//println ("Forcing str_1_SYMSTRING = 21");
						while (pc.header != null) {
							pc._addDet(Comparator.EQ, v.getSymbolicLength(), 21);
							if (scg.isSatisfiable(pc)) {
								//println ("Solvable:");
								
								//println ("is Sat");
								scg.solve(pc);
								PathCondition.flagSolved = true;
								if (pc.header != null) {
									//println(pc.header.toString());
								}
							}
							else {
								//println ("Not solvable " + v.getSymbolicLength());
							}
							pc.header = pc.header.and.and;
						}
						throw new RuntimeException("done");
					}
				}
			}*/
			return false;
		}
		//println ("[preprocess] Preprocessor done");
		return true;
	}
	
	private static void forceLengthsSame (Vertex v1, Vertex v2, PathCondition pc) {
		if (v1.constant) {
			if (v2.constant) {
				pc._addDet(Comparator.EQ, v1.getLength(), new IntegerConstant(v2.getLength()));
			}
			else {
				pc._addDet(Comparator.EQ, v1.getLength(), v2.getSymbolicLength());
			}
		}
		else {
			if (v2.constant) {
				pc._addDet(Comparator.EQ, v1.getSymbolicLength(), new IntegerConstant(v2.getLength()));
			}
			else {
				pc._addDet(Comparator.EQ, v1.getSymbolicLength(), v2.getSymbolicLength());
			}
		}
	}
	
}

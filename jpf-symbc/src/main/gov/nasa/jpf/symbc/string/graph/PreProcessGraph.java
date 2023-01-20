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

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.string.StringComparator;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringUtility;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfInteger;
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;
import gov.nasa.jpf.util.LogManager;
import java.util.logging.Logger;

/**
 * This class does the preprocessing of the StringGraph
 */
public class PreProcessGraph {
  static Logger logger = LogManager.getLogger("stringsolver");
	public static final int MAXIMUM_LENGTH = 30;
	private static SymbolicConstraintsGeneral scg;
	
	//TODO: Add support for NoCharAt and LastIndexOf
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
	public static boolean preprocess (StringGraph stringGraph, PathCondition pathCondition) {
		
		scg = new SymbolicConstraintsGeneral();
		
		if(!scg.isSatisfiable(pathCondition)) {logger.info("unsat here");};
		
		if (!handleEquality(stringGraph, pathCondition)) {
			//println ("handleEquality returned false");
			return false;
		}
		if (!handleBasics(stringGraph, pathCondition)) {
			//println ("handleBasics returned false");
			return false;
		}
		if (!handleBooleanConstraints(stringGraph, pathCondition)) {
			//println ("handleBooleanConstraints returned false");
			return false;
		}
		if (!handleConcat(stringGraph, pathCondition)) {
			//println ("handleConcat returned false");
			return false;
		}
		if (!handleCharAt(stringGraph, pathCondition)) {
			//println ("handleCharAt returned false");
			return false;
		}
		if (!handleSubstring(stringGraph, pathCondition)) {
			//println ("handleSubstring returned false");
			return false;
		}
		if (!handleIndexOf(stringGraph, pathCondition)) {
			//println ("handleIndexOf returned false");
			return false;
		}
		if (!handleLastIndexOf(stringGraph, pathCondition)) {
			//println ("handleIndexOf returned false");
			return false;
		}
		if (!handleConstants(stringGraph, pathCondition)) {
			//println ("handleConstants returned false");
			return false;
		}
		if (!handleTrim(stringGraph, pathCondition)) {
			//println ("handleTrim returned false");
			return false;
		}
		if (scg.isSatisfiable(pathCondition)) {
			scg.solve(pathCondition);
			PathCondition.flagSolved = true;
			//println (pathCondition.toString());
			return true;
		} else {
			//println (pathCondition.toString());
			return false;
		}
	}
	
	private static boolean handleBasics (StringGraph g, PathCondition pc) {
		for (Vertex v: g.getVertices()) {
			/* according to gideon's thesis, this applies only to non-constant
			 * vertexes (page 55, table 3.1)*/
			if(!v.constant) { 
				pc._addDet(Comparator.GE, v.getSymbolicLength(), 1);
				pc._addDet(Comparator.LE, v.getSymbolicLength(), MAXIMUM_LENGTH);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOf (StringGraph g, PathCondition pc) {
		if (!handleBasicIndexOf(g, pc)) {
			//println ("handleBasicIndexOf returned false");
			return false;
		}
		if (!handleIndexOfDependencies(g, pc)) {
			//println ("handleIndexOfDependencies returned false");
			return false;
		}
		if (!handleIndexOfStr(g, pc)) {
			//println ("handleIndexOfStr returned false");
			return false;
		}
		if (!handleIndexOfStrInt(g, pc)) {
			//println ("handleIndexOfStr returned false");
			return false;
		}
		if (!handleIndexOfChar(g, pc)) {
			//println ("handleIndexOfStr returned false");
			return false;
		}
		if (!handleIndexOfCharInt(g, pc)) {
			//println ("handleIndexOfStr returned false");
			return false;
		}
		
		return true;
	}
	
	private static boolean handleLastIndexOf (StringGraph g, PathCondition pc) {
		if (!handleBasicLastIndexOf(g, pc)) {
			//println ("handleBasicIndexOf returned false");
			return false;
		}
		if (!handleLastIndexOfDependencies(g, pc)) {
			//println ("handleIndexOfDependencies returned false");
			return false;
		}
		if (!handleLastIndexOfChar(g, pc)) {
			//println ("handleIndexOfStr returned false");
			return false;
		}
		if (!handleLastIndexOfCharInt(g, pc)) {
			//println ("handleIndexOfStr returned false");
			return false;
		}
		/*if (!handleIndexOfStr(g, pc)) {
			//println ("handleIndexOfStr returned false");
			return false;
		}
		if (!handleIndexOfStrInt(g, pc)) {
			//println ("handleIndexOfStr returned false");
			return false;
		}
		
		if (!handleIndexOfCharInt(g, pc)) {
			//println ("handleIndexOfStr returned false");
			return false;
		}*/
		
		return true;
	}
	
	private static boolean handleTrim (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (e instanceof EdgeTrimEqual) {
				pc._addDet (Comparator.LE, e.getDest().getSymbolicLength(), e.getSource().getSymbolicLength());
				//TODO discover what is the bug mentioned below.  
				//Fix a stupid bug in Trim of JSA
				if(SymbolicInstructionFactory.string_dp[0].equals("automata")) {
					pc._addDet (Comparator.GE, e.getDest().getSymbolicLength(), new IntegerConstant(2));
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfChar (StringGraph g, PathCondition pc) {
		if (!handleIndexOfCharBasics(g, pc)) {
			//println ("handleIndexOfNotContains returned false");
			return false;
		}
		if (!handleIndexOfCharNotContains(g, pc)) {
			//println ("handleIndexOfNotContains returned false");
			return false;
		}
		if (!handleIndexOfCharStartsWith(g, pc)) {
			//println ("handleIndexOfStartsWith returned false");
			return false;
		}
		if (!handleIndexOfCharNotStartsWith(g, pc)) {
			//println ("handleIndexOfNotStartsWith returned false");
			return false;
		}
		if (!handleIndexOfCharContains(g, pc)) {
			//println ("handleIndexOfCharContains returned false");
			return false;
		}
		if (!handleIndexOfCharCharAt(g, pc)) {
			//println ("handleIndexOfCharAt returned false");
			return false;
		}
		return true;
	}
	
	private static boolean handleIndexOfCharBasics (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeIndexOfChar)) continue;
			EdgeIndexOfChar eca = (EdgeIndexOfChar) e;
			pc._addDet(Comparator.GE, eca.getIndex().getExpression(), SymbolicStringConstraintsGeneral.MIN_CHAR);
			pc._addDet(Comparator.LT, eca.getIndex().getExpression(), SymbolicStringConstraintsGeneral.MAX_CHAR);
			pc._addDet(Comparator.LE, eca.getIndex(), MAXIMUM_LENGTH);
		}
		return true;
	}
	
	private static boolean handleLastIndexOfChar (StringGraph g, PathCondition pc) {
		if (!handleLastIndexOfCharBasics(g, pc)) {
			//println ("handleIndexOfNotContains returned false");
			return false;
		}
		if (!handleLastIndexOfCharNotContains(g, pc)) {
			//println ("handleIndexOfNotContains returned false");
			return false;
		}
		if (!handleLastIndexOfCharContains(g, pc)) {
			//println ("handleIndexOfCharContains returned false");
			return false;
		}
		if (!handleLastIndexOfCharCharAt(g, pc)) {
			//println ("handleIndexOfCharAt returned false");
			return false;
		}
		if (!handleLastIndexOfCharEndsWith(g, pc)) {
			//println ("handleIndexOfStartsWith returned false");
			return false;
		}
		if (!handleLastIndexOfCharNotEndsWith(g, pc)) {
			//println ("handleIndexOfNotStartsWith returned false");
			return false;
		}
		
		return true;
	}
	
	private static boolean handleLastIndexOfCharBasics (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeLastIndexOfChar)) continue;
			EdgeLastIndexOfChar eca = (EdgeLastIndexOfChar) e;
			pc._addDet(Comparator.GE, eca.getIndex().getExpression(), SymbolicStringConstraintsGeneral.MIN_CHAR);
			pc._addDet(Comparator.LT, eca.getIndex().getExpression(), SymbolicStringConstraintsGeneral.MAX_CHAR);
			pc._addDet(Comparator.LE, eca.getIndex(), MAXIMUM_LENGTH);
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharInt (StringGraph g, PathCondition pc) {
		if (!handleLastIndexOfCharIntBasics(g, pc)) {
			//println ("handleLastIndexOfCharIntBasics");
			return false;
		}
		if (!handleLastIndexOfCharIntNotContains(g, pc)) {
			//println ("handleIndexOfNotContains returned false");
			return false;
		}
		if (!handleLastIndexOfCharIntCharAt(g, pc)) {
			//println ("handleIndexOfCharAt returned false");
			return false;
		}
		if (!handleLastIndexOfCharIntEndsWith(g, pc)) {
			//println ("handleIndexOfStartsWith returned false");
			return false;
		}
		if (!handleLastIndexOfCharIntNotEndsWith(g, pc)) {
			//println ("handleIndexOfNotStartsWith returned false");
			return false;
		}
		
		return true;
	}
	
	private static boolean handleLastIndexOfCharIntBasics (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeLastIndexOfChar)) continue;
			EdgeLastIndexOfChar eca = (EdgeLastIndexOfChar) e;
			pc._addDet(Comparator.GE, eca.getIndex().getExpression(), SymbolicStringConstraintsGeneral.MIN_CHAR);
			pc._addDet(Comparator.LT, eca.getIndex().getExpression(), SymbolicStringConstraintsGeneral.MAX_CHAR);
			pc._addDet(Comparator.LE, eca.getIndex(), MAXIMUM_LENGTH);
		}
		return true;
	}

	
	private static boolean handleSubstring (StringGraph g, PathCondition pc) {
		if (!handleSubstring1Basic(g, pc)) {
			//println ("handleSubstring1Basic returned false");
			return false;
		}
		if (!handleSubstring1IndexOf(g, pc)) {
			//println ("handleSubstring1IndexOf returned false");
			return false;
		}
		if (!handleSubstring1CharAt(g, pc)) {
			//println ("handleSubstring1CharAt returned false");
			return false;
		}
		if (!handleSubstring2Basic(g, pc)) {
			//println ("handleSubstring2Basic returned false");
			return false;
		}
		if (!handleSubstring2CharAt(g, pc)) {
			//println ("handleSubstring2CharAt returned false");
			return false;
		}
		if (!handleSubstring2IndexOf(g, pc)) {
			//println ("handleSubstring2CharAt returned false");
			return false;
		}
		return true;
	}
	
	private static boolean handleSubstring1CharAt(StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				EdgeCharAt eca = null;
				EdgeSubstring1Equal es1e = null;
				
				if (e1 instanceof EdgeCharAt && e2 instanceof EdgeSubstring1Equal) {
					eca = (EdgeCharAt) e1;
					es1e = (EdgeSubstring1Equal) e2;
				} else if (e2 instanceof EdgeCharAt && e1 instanceof EdgeSubstring1Equal) {
					eca = (EdgeCharAt) e2;
					es1e = (EdgeSubstring1Equal) e1;
				} else {
					continue;
				}
				
				if (es1e.getDest().isConstant()) {
					String solution = e1.getDest().getSolution();
					for (int k = 0; k < solution.length(); k++) {
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.NE, new IntegerConstant(es1e.getArgument1() + k)));
						loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(solution.charAt(k))));
						pc._addDet(loic);
					}
				}
			}
			//println (pc.toString());
		}
		return true;
	}
	
	private static boolean handleSubstring1IndexOf(StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				EdgeIndexOf eio = null;
				EdgeSubstring1Equal es1e = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeSubstring1Equal) {
					eio = (EdgeIndexOf) e1;
					es1e = (EdgeSubstring1Equal) e2;
				} else if (e2 instanceof EdgeIndexOf && e1 instanceof EdgeSubstring1Equal) {
					eio = (EdgeIndexOf) e2;
					es1e = (EdgeSubstring1Equal) e1;
				} else {
					continue;
				}
				
				if (eio.getIndex().getExpression() instanceof StringConstant && es1e.getDest().isConstant()) {
					int possiblePos = es1e.getDest().getSolution().indexOf(eio.getIndex().getExpression().solution());
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
		}
		return true;
	}
	
	private static boolean handleSubstring2IndexOf(StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				EdgeIndexOf eio = null;
				EdgeSubstring2Equal es2e = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeSubstring2Equal) {
					eio = (EdgeIndexOf) e1;
					es2e = (EdgeSubstring2Equal) e2;
				} else if (e2 instanceof EdgeIndexOf && e1 instanceof EdgeSubstring2Equal) {
					eio = (EdgeIndexOf) e2;
					es2e = (EdgeSubstring2Equal) e1;
				} else {
					continue;
				}
				
				if (eio.getIndex().getExpression() instanceof StringConstant && es2e.getDest().isConstant()) {
					int possiblePos = es2e.getDest().getSolution().indexOf(eio.getIndex().getExpression().solution());
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
		}
		return true;
	}
	
	private static boolean handleSubstring1Basic (StringGraph g, PathCondition pc) {
		for (Edge edge: g.getEdges()){
			if (!(edge instanceof EdgeSubstring1Equal)) {continue;}
			EdgeSubstring1Equal es1e = (EdgeSubstring1Equal) edge;
			pc._addDet (Comparator.LE, edge.getDest().getSymbolicLength(), edge.getSource().getSymbolicLength());
			if (es1e.getArgument1Symbolic() != null) {
				pc._addDet(Comparator.GE, es1e.getArgument1Symbolic(), 0);
			} else {
				pc._addDet(Comparator.GE, edge.getSource().getSymbolicLength(), new IntegerConstant(es1e.a1)._plus(edge.getDest().getSymbolicLength()));
			}
		}
		return true;
	}
	
	private static boolean handleSubstring2Basic (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()){
			if (!(e instanceof EdgeSubstring2Equal)) {continue;}
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
		return true;
	}
	
	private static boolean handleSubstring2CharAt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeSubstring2Equal es2e = null;
				EdgeCharAt eca = null;
				
				if (e1 instanceof EdgeSubstring2Equal && e2 instanceof EdgeCharAt) {
					es2e = (EdgeSubstring2Equal) e1;
					eca = (EdgeCharAt) e2;
				} else if (e2 instanceof EdgeSubstring2Equal && e1 instanceof EdgeCharAt) {
					es2e = (EdgeSubstring2Equal) e2;
					eca = (EdgeCharAt) e1;
				} else {
					continue;
				}
				
				if (es2e.getDest().isConstant()) {
					String solution = e1.getDest().getSolution();
					for (int k = 0; k < solution.length(); k++) {
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.NE, new IntegerConstant(es2e.getArgument1() + k)));
						loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(solution.charAt(k))));
						pc._addDet(loic);
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharNotContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar eioc = null;
				EdgeNotContains enc = null;
				
				if (e1 instanceof EdgeIndexOfChar && e2 instanceof EdgeNotContains) {
					eioc = (EdgeIndexOfChar) e1;
					enc = (EdgeNotContains) e2;
				} else if (e2 instanceof EdgeIndexOfChar && e1 instanceof EdgeNotContains) {
					eioc = (EdgeIndexOfChar) e2;
					enc = (EdgeNotContains) e1;
				} else {
					continue;
				}
				
				if (!enc.getDest().isConstant()) {continue;}
				String constant = enc.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharNotContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeLastIndexOfChar eioc = null;
				EdgeNotContains enc = null;
				
				if (e1 instanceof EdgeLastIndexOfChar && e2 instanceof EdgeNotContains) {
					eioc = (EdgeLastIndexOfChar) e1;
					enc = (EdgeNotContains) e2;
				} else if (e2 instanceof EdgeLastIndexOfChar && e1 instanceof EdgeNotContains) {
					eioc = (EdgeLastIndexOfChar) e2;
					enc = (EdgeNotContains) e1;
				} else {
					continue;
				}
				
				if (!enc.getDest().isConstant()) {continue;}
				String constant = enc.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharIntNotContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeLastIndexOfChar2 eioc = null;
				EdgeNotContains enc = null;
				
				if (e1 instanceof EdgeLastIndexOfChar2 && e2 instanceof EdgeNotContains) {
					eioc = (EdgeLastIndexOfChar2) e1;
					enc = (EdgeNotContains) e2;
				} else if (e2 instanceof EdgeLastIndexOfChar2 && e1 instanceof EdgeNotContains) {
					eioc = (EdgeLastIndexOfChar2) e2;
					enc = (EdgeNotContains) e1;
				} else {
					continue;
				}
				
				if (!enc.getDest().isConstant()) {continue;}
				String constant = enc.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharIntNotContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar2 eioc = null;
				EdgeNotContains enc = null;
				
				if (e1 instanceof EdgeIndexOfChar2 && e2 instanceof EdgeNotContains) {
					eioc = (EdgeIndexOfChar2) e1;
					enc = (EdgeNotContains) e2;
				} else if (e2 instanceof EdgeIndexOfChar2 && e1 instanceof EdgeNotContains) {
					eioc = (EdgeIndexOfChar2) e2;
					enc = (EdgeNotContains) e1;
				} else {
					continue;
				}
				
				if (!enc.getDest().isConstant()) {continue;}
				String constant = enc.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharStartsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar eioc = null;
				EdgeStartsWith esw = null;
				
				if (e1 instanceof EdgeIndexOfChar && e2 instanceof EdgeStartsWith) {
					eioc = (EdgeIndexOfChar) e1;
					esw = (EdgeStartsWith) e2;
				} else if (e2 instanceof EdgeIndexOfChar && e1 instanceof EdgeStartsWith) {
					eioc = (EdgeIndexOfChar) e2;
					esw = (EdgeStartsWith) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.EQ, new IntegerConstant(0)));
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.EQ, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, new IntegerConstant(0)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharEndsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeLastIndexOfChar eioc = null;
				EdgeEndsWith esw = null;
				
				if (e1 instanceof EdgeLastIndexOfChar && e2 instanceof EdgeEndsWith) {
					eioc = (EdgeLastIndexOfChar) e1;
					esw = (EdgeEndsWith) e2;
				} else if (e2 instanceof EdgeLastIndexOfChar && e1 instanceof EdgeEndsWith) {
					eioc = (EdgeLastIndexOfChar) e2;
					esw = (EdgeEndsWith) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				//TODO: Test
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.EQ, esw.getSource().getSymbolicLength()._minus(1)));
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.EQ, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, esw.getSource().getSymbolicLength()._minus(1)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharIntEndsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeLastIndexOfChar2 eioc = null;
				EdgeEndsWith esw = null;
				
				if (e1 instanceof EdgeLastIndexOfChar2 && e2 instanceof EdgeEndsWith) {
					eioc = (EdgeLastIndexOfChar2) e1;
					esw = (EdgeEndsWith) e2;
				} else if (e2 instanceof EdgeLastIndexOfChar2 && e1 instanceof EdgeEndsWith) {
					eioc = (EdgeLastIndexOfChar2) e2;
					esw = (EdgeEndsWith) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				//TODO: Test
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.EQ, esw.getSource().getSymbolicLength()._minus(1)));
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.EQ, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, esw.getSource().getSymbolicLength()._minus(1)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharIntStartsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar2 eioc = null;
				EdgeStartsWith esw = null;
				
				if (e1 instanceof EdgeIndexOfChar2 && e2 instanceof EdgeStartsWith) {
					eioc = (EdgeIndexOfChar2) e1;
					esw = (EdgeStartsWith) e2;
				} else if (e2 instanceof EdgeIndexOfChar2 && e1 instanceof EdgeStartsWith) {
					eioc = (EdgeIndexOfChar2) e2;
					esw = (EdgeStartsWith) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getMinDist(), Comparator.GT, new IntegerConstant(0)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.EQ, new IntegerConstant(0)));
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getMinDist(), Comparator.GT, new IntegerConstant(0)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.EQ, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, new IntegerConstant(0)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharNotStartsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar eioc = null;
				EdgeNotStartsWith esw = null;
				
				if (e1 instanceof EdgeIndexOfChar && e2 instanceof EdgeNotStartsWith) {
					eioc = (EdgeIndexOfChar) e1;
					esw = (EdgeNotStartsWith) e2;
				} else if (e2 instanceof EdgeIndexOfChar && e1 instanceof EdgeNotStartsWith) {
					eioc = (EdgeIndexOfChar) e2;
					esw = (EdgeNotStartsWith) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, new IntegerConstant(0)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharNotEndsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeLastIndexOfChar eioc = null;
				EdgeNotEndsWith esw = null;
				
				if (e1 instanceof EdgeLastIndexOfChar && e2 instanceof EdgeNotEndsWith) {
					eioc = (EdgeLastIndexOfChar) e1;
					esw = (EdgeNotEndsWith) e2;
				} else if (e2 instanceof EdgeLastIndexOfChar && e1 instanceof EdgeNotEndsWith) {
					eioc = (EdgeLastIndexOfChar) e2;
					esw = (EdgeNotEndsWith) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, esw.getSource().getSymbolicLength()._minus(1)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharIntNotEndsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeLastIndexOfChar2 eioc = null;
				EdgeNotEndsWith esw = null;
				
				if (e1 instanceof EdgeLastIndexOfChar2 && e2 instanceof EdgeNotEndsWith) {
					eioc = (EdgeLastIndexOfChar2) e1;
					esw = (EdgeNotEndsWith) e2;
				} else if (e2 instanceof EdgeLastIndexOfChar2 && e1 instanceof EdgeNotEndsWith) {
					eioc = (EdgeLastIndexOfChar2) e2;
					esw = (EdgeNotEndsWith) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, esw.getSource().getSymbolicLength()._minus(1)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharIntNotStartsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar2 eioc = null;
				EdgeNotStartsWith esw = null;
				
				if (e1 instanceof EdgeIndexOfChar2 && e2 instanceof EdgeNotStartsWith) {
					eioc = (EdgeIndexOfChar2) e1;
					esw = (EdgeNotStartsWith) e2;
				} else if (e2 instanceof EdgeIndexOfChar2 && e1 instanceof EdgeNotStartsWith) {
					eioc = (EdgeIndexOfChar2) e2;
					esw = (EdgeNotStartsWith) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				if (constant.length() != 1) {continue;}
				char character = constant.charAt(0);
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getMinDist(), Comparator.GT, new IntegerConstant(0)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, new IntegerConstant(0)));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar eioc = null;
				EdgeContains esw = null;
				
				if (e1 instanceof EdgeIndexOfChar && e2 instanceof EdgeContains) {
					eioc = (EdgeIndexOfChar) e1;
					esw = (EdgeContains) e2;
				} else if (e2 instanceof EdgeIndexOfChar && e1 instanceof EdgeContains) {
					eioc = (EdgeIndexOfChar) e2;
					esw = (EdgeContains) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				for (int k = 0; k < constant.length(); k++) {
					char character = constant.charAt(k);
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
					loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.GT, new IntegerConstant(-1)));
					pc._addDet(loic);
				}
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeLastIndexOfChar eioc = null;
				EdgeContains esw = null;
				
				if (e1 instanceof EdgeLastIndexOfChar && e2 instanceof EdgeContains) {
					eioc = (EdgeLastIndexOfChar) e1;
					esw = (EdgeContains) e2;
				} else if (e2 instanceof EdgeLastIndexOfChar && e1 instanceof EdgeContains) {
					eioc = (EdgeLastIndexOfChar) e2;
					esw = (EdgeContains) e1;
				} else {
					continue;
				}
				
				if (!esw.getDest().isConstant()) {continue;}
				String constant = esw.getDest().getSolution();
				for (int k = 0; k < constant.length(); k++) {
					char character = constant.charAt(k);
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, new IntegerConstant(character)));
					loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.GT, new IntegerConstant(-1)));
					pc._addDet(loic);
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharCharAt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar eioc = null;
				EdgeCharAt esw = null;
				
				if (e1 instanceof EdgeIndexOfChar && e2 instanceof EdgeCharAt) {
					eioc = (EdgeIndexOfChar) e1;
					esw = (EdgeCharAt) e2;
				} else if (e2 instanceof EdgeIndexOfChar && e1 instanceof EdgeCharAt) {
					eioc = (EdgeIndexOfChar) e2;
					esw = (EdgeCharAt) e1;
				} else {
					continue;
				}
				
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, esw.index));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.EQ, esw.value));
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, esw.value));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.LE, esw.index));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharCharAt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeLastIndexOfChar eioc = null;
				EdgeCharAt esw = null;
				
				if (e1 instanceof EdgeLastIndexOfChar && e2 instanceof EdgeCharAt) {
					eioc = (EdgeLastIndexOfChar) e1;
					esw = (EdgeCharAt) e2;
				} else if (e2 instanceof EdgeLastIndexOfChar && e1 instanceof EdgeCharAt) {
					eioc = (EdgeLastIndexOfChar) e2;
					esw = (EdgeCharAt) e1;
				} else {
					continue;
				}
				
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, esw.index));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.EQ, esw.value));
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, esw.value));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.GE, esw.index)); //TODO: Test
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharIntCharAt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeLastIndexOfChar2 eioc = null;
				EdgeCharAt esw = null;
				
				if (e1 instanceof EdgeLastIndexOfChar2 && e2 instanceof EdgeCharAt) {
					eioc = (EdgeLastIndexOfChar2) e1;
					esw = (EdgeCharAt) e2;
				} else if (e2 instanceof EdgeLastIndexOfChar2 && e1 instanceof EdgeCharAt) {
					eioc = (EdgeLastIndexOfChar2) e2;
					esw = (EdgeCharAt) e1;
				} else {
					continue;
				}
				
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(esw.index, Comparator.GT, eioc.getIndex().getMinDist()));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, esw.index));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.EQ, esw.value));
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(esw.index, Comparator.GT, eioc.getIndex().getMinDist()));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, esw.value));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.LE, esw.index)); //TODO: Test
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharIntCharAt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar2 eioc = null;
				EdgeCharAt eca = null;
				
				if (e1 instanceof EdgeIndexOfChar2 && e2 instanceof EdgeCharAt) {
					eioc = (EdgeIndexOfChar2) e1;
					eca = (EdgeCharAt) e2;
				} else if (e2 instanceof EdgeIndexOfChar2 && e1 instanceof EdgeCharAt) {
					eioc = (EdgeIndexOfChar2) e2;
					eca = (EdgeCharAt) e1;
				} else {
					continue;
				}
				
				//LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				/*loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, esw.index));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.EQ, esw.value));
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex().getExpression(), Comparator.NE, esw.value));
				loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.LE, esw.index));*/
				
				IntegerExpression se = eioc.getIndex().getExpression();
				if (se instanceof IntegerConstant) {
					//println ("[preprocess] Path followed 2");
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(se, Comparator.EQ, eca.getValue()) );
					loic.addToList(new LinearIntegerConstraint(eioc.getIndex(), Comparator.NE, eca.getIndex()));
					loic.comment = "charAt and indexOfCharInt";
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStr (StringGraph g, PathCondition pc) {
		if (!handleIndexOfStrNotContains(g, pc)) {
			//println ("handleIndexOfNotContains returned false");
			return false;
		}
		if (!handleIndexOfStrStartsWith(g, pc)) {
			//println ("handleIndexOfStartsWith returned false");
			return false;
		}
		if (!handleIndexOfStrNotStartsWith(g, pc)) {
			//println ("handleIndexOfNotStartsWith returned false");
			return false;
		}
		if (!handleIndexOfStrContains(g, pc)) {
			//println ("handleIndexOfContains returned false");
			return false;
		}
		if (!handleIndexOfStrCharAt(g, pc)) {
			//println ("handleIndexOfCharAt returned false");
			return false;
		}
		return true;
	}
	
	private static boolean handleIndexOfStrInt (StringGraph g, PathCondition pc) {
		if (!handleIndexOfStrIntNotContains(g, pc)) {
			//println ("handleIndexOfNotContains returned false");
			return false;
		}
		if (!handleIndexOfStrIntStartsWith(g, pc)) {
			//println ("handleIndexOfStartsWith returned false");
			return false;
		}
		if (!handleIndexOfStrIntNotStartsWith(g, pc)) {
			//println ("handleIndexOfNotStartsWith returned false");
			return false;
		}
		if (!handleIndexOfStrIntCharAt(g, pc)) {
			//println ("handleIndexOfCharAt returned false");
			return false;
		}
		return true;
	}
	
	private static boolean handleIndexOfCharInt (StringGraph g, PathCondition pc) {
		if (!handleIndexOfCharIntBasics (g, pc)) {
			//println ("handleIndexOfCharIntBasics");
			return false;
		}
		if (!handleIndexOfCharIntNotContains(g, pc)) {
			//println ("handleIndexOfNotContains returned false");
			return false;
		}
		if (!handleIndexOfCharIntStartsWith(g, pc)) {
			//println ("handleIndexOfStartsWith returned false");
			return false;
		}
		if (!handleIndexOfCharIntNotStartsWith(g, pc)) {
			//println ("handleIndexOfNotStartsWith returned false");
			return false;
		}
		if (!handleIndexOfCharIntCharAt(g, pc)) {
			//println ("handleIndexOfCharAt returned false");
			return false;
		}
		return true;
	}
	
	private static boolean handleIndexOfDependencies (StringGraph g, PathCondition pc) {
		if (!handleIndexOfStrDependencies(g, pc)) {
			//println ("handleIndexOfStrDependencies returned false");
			return false;
		}
		if (!handleIndexOfCharDependencies(g, pc)) {
			//println ("handleIndexOfCharDependencies returned false");
			return false;
		}
		if (!handleIndexOfCharIntDependencies(g, pc)) {
			//println ("handleIndexOfCharIntDependencies returned false");
			return false;
		}
		if (!handleIndexOfStrIntBasics(g, pc)) {
			//println ("handleIndexOfStrIntBasics returned false");
			return false;
		}
		if (!handleIndexOfCharIntBasics(g, pc)) {
			//println ("handleIndexOfCharIntBasics returned false");
			return false;
		}
		if (!handleIndexOfStrIntDependencies(g, pc)) {
			//println ("handleIndexOfStrIntDependencies returned false");
			return false;
		}
		if (!handleIndexOfStrIndexOfChar(g, pc)) {
			//println ("handleIndexOfStrIndexOfChar returned false");
			return false;
		}
		if (!handleIndexOfStrIndexOfCharInt(g, pc)) {
			//println ("handleIndexOfStrIndexOfChar2 returned false");
			return false;
		}
		if (!handleIndexOfStrIndexOfStrInt(g, pc)) {
			//println ("handleIndexOfStrIndexOfChar2 returned false");
			return false;
		}
		if (!handleIndexOfStrIntIndexOfChar(g, pc)) {
			//println ("handleIndexOfStrIndexOfChar2 returned false");
			return false;
		}
		if (!handleIndexOfStrIntIndexOfCharInt(g, pc)) {
			//println ("handleIndexOfStrIndexOfChar2 returned false");
			return false;
		}
		//TODO: Test from here
		if (!handleIndexOfCharIndexOfCharInt(g, pc)) {
			//println ("handleIndexOfStrIndexOfChar2 returned false");
			return false;
		}
		return true;
	}
	
	private static boolean handleLastIndexOfDependencies (StringGraph g, PathCondition pc) {
		if (!handleLastIndexOfCharDependencies(g, pc)) {
			//println ("handleIndexOfStrDependencies returned false");
			return false;
		}
		if (!handleLastIndexOfCharIntDependencies(g, pc)) {
			//println ("handleIndexOfStrDependencies returned false");
			return false;
		}
		return true;
	}
	
	private static boolean handleIndexOfStrDependencies (StringGraph g, PathCondition pc) {
		//TODO: Think more of this
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				if (!(e1 instanceof EdgeIndexOf && e2 instanceof EdgeIndexOf)) { continue; }
				
				EdgeIndexOf eio1 = (EdgeIndexOf) e1;
				EdgeIndexOf eio2 = (EdgeIndexOf) e2;
				
				if (e1.getDest().equals(e2.getDest())) {
					pc._addDet(Comparator.EQ, eio1.sioi, eio2.sioi);
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = e1.getDest().getSolution();
					String constant2 = e2.getDest().getSolution();
					for (int k = 0; k < constant1.length(); k++) {
						for (int l = k; l < constant2.length(); l++) {
							if (constant1.charAt(k) != constant2.charAt(l)) {
								LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
								loic.addToList(new LinearIntegerConstraint(eio1.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio2.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(l), Comparator.NE, eio2.getIndex()._plus(k)));
								pc._addDet(loic);
							}
						}
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharDependencies (StringGraph g, PathCondition pc) {
		//TODO: Think more of this
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				if (!(e1 instanceof EdgeLastIndexOfChar && e2 instanceof EdgeLastIndexOfChar)) { continue; }
				
				EdgeLastIndexOfChar eio1 = (EdgeLastIndexOfChar) e1;
				EdgeLastIndexOfChar eio2 = (EdgeLastIndexOfChar) e2;
				
				if (e1.getDest().equals(e2.getDest())) {
					pc._addDet(Comparator.EQ, eio1.sioi, eio2.sioi);
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = e1.getDest().getSolution();
					String constant2 = e2.getDest().getSolution();
					for (int k = 0; k < constant1.length(); k++) {
						for (int l = k; l < constant2.length(); l++) {
							if (constant1.charAt(k) != constant2.charAt(l)) {
								LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
								loic.addToList(new LinearIntegerConstraint(eio1.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio2.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(l), Comparator.NE, eio2.getIndex()._plus(k)));
								pc._addDet(loic);
							}
						}
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleLastIndexOfCharIntDependencies (StringGraph g, PathCondition pc) {
		//TODO: Think more of this
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				if (!(e1 instanceof EdgeLastIndexOfChar2 && e2 instanceof EdgeLastIndexOfChar2)) { continue; }
				
				EdgeLastIndexOfChar2 eio1 = (EdgeLastIndexOfChar2) e1;
				EdgeLastIndexOfChar2 eio2 = (EdgeLastIndexOfChar2) e2;
				
				if (e1.getDest().equals(e2.getDest())) {
					pc._addDet(Comparator.EQ, eio1.sioi, eio2.sioi);
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = e1.getDest().getSolution();
					String constant2 = e2.getDest().getSolution();
					for (int k = 0; k < constant1.length(); k++) {
						for (int l = k; l < constant2.length(); l++) {
							if (constant1.charAt(k) != constant2.charAt(l)) {
								LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
								loic.addToList(new LinearIntegerConstraint(eio1.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio2.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(l), Comparator.NE, eio2.getIndex()._plus(k)));
								pc._addDet(loic);
							}
						}
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIndexOfStrInt (StringGraph g, PathCondition pc) {
		
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf eio = null;
				EdgeIndexOf2 eio2 = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeIndexOf2) {
					eio = (EdgeIndexOf) e1;
					eio2 = (EdgeIndexOf2) e2;
				}
				else if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeIndexOf) {
					eio = (EdgeIndexOf) e2;
					eio2 = (EdgeIndexOf2) e1;
				} else 
				{ continue; }
				
				if (e1.getDest().equals(e2.getDest())) {
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eio2.getIndex().getMinIndex(), Comparator.GE, eio.getIndex()));
					loic.addToList(new LinearIntegerConstraint(eio.sioi, Comparator.EQ, eio2.sioi));
					pc._addDet(loic);
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = e1.getDest().getSolution();
					String constant2 = e2.getDest().getSolution();
					for (int k = 0; k < constant1.length(); k++) {
						for (int l = k; l < constant2.length(); l++) {
							if (constant1.charAt(k) != constant2.charAt(l)) {
								//TODO: Test if two overlaps
								LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
								loic.addToList(new LinearIntegerConstraint(eio2.getIndex().getMinIndex(), Comparator.GE, eio.getIndex()));
								loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio2.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio.getIndex()._plus(l), Comparator.NE, eio2.getIndex()._plus(k)));
								pc._addDet(loic);
							}
						}
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIntBasics (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeIndexOf2)) {continue;}
			EdgeIndexOf2 eio = (EdgeIndexOf2) e;
			LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.GE, eio.getIndex().getMinIndex()));
			loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
			pc._addDet(loic);
			pc._addDet(Comparator.LE, eio.getIndex(), new IntegerConstant(MAXIMUM_LENGTH));
			//pc._addDet(Comparator.GE, eio.getIndex(), eio.getIndex().getMinIndex());
		}
		return true;
	}
	
	private static boolean handleIndexOfCharIntBasics (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeIndexOfChar2)) {continue;}
			EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e;
			pc._addDet(Comparator.LE, eio.getIndex(), new IntegerConstant(MAXIMUM_LENGTH));
			pc._addDet(Comparator.GE, eio.getIndex(), eio.getIndex().getMinDist());
			pc._addDet(Comparator.LE, eio.getIndex().getExpression(), SymbolicStringConstraintsGeneral.MAX_CHAR);
			pc._addDet(Comparator.GE, eio.getIndex().getExpression(), SymbolicStringConstraintsGeneral.MIN_CHAR);
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIntDependencies (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				if (!(e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeIndexOf2)) { continue; }
				//println ("hierso v1");
				EdgeIndexOf2 eio1 = (EdgeIndexOf2) e1;
				EdgeIndexOf2 eio2 = (EdgeIndexOf2) e2;
				
				if (e1.getDest().equals(e2.getDest())) {
					pc._addDet(Comparator.EQ, eio1.sioi, eio2.sioi);
					pc._addDet(Comparator.EQ, eio1.getIndex().getMinIndex(), eio2.getIndex().getMinIndex());
				}
				else { // TODO: why not isConstant?*/
					if (!(eio1.getIndex().getExpression() instanceof StringConstant && eio2.getIndex().getExpression() instanceof StringConstant)) { continue; }
					
					String constant1 = e1.getDest().getSolution();
					String constant2 = e2.getDest().getSolution();
					for (int k = 0; k < constant1.length(); k++) {
						for (int l = k; l < constant2.length(); l++) {
							if (constant1.charAt(k) != constant2.charAt(l)) {
								LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
								loic.addToList(new LinearIntegerConstraint(eio1.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio2.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(k), Comparator.NE, eio2.getIndex()._plus(l)));
								loic.comment = "indexOfStrInt and indexOfStrInt p1";
								pc._addDet(loic);
							}
						}
					}
					constant1 = e2.getDest().getSolution();
					constant2 = e1.getDest().getSolution();
					for (int k = 0; k < constant1.length(); k++) {
						for (int l = k; l < constant2.length(); l++) {
							if (constant1.charAt(k) != constant2.charAt(l)) {
								LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
								loic.addToList(new LinearIntegerConstraint(eio2.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio1.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
								loic.addToList(new LinearIntegerConstraint(eio2.getIndex()._plus(k), Comparator.NE, eio1.getIndex()._plus(l)));
								loic.comment = "indexOfStrInt and indexOfStrInt p2";
								pc._addDet(loic);
							}
						}
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIndexOfChar (StringGraph g, PathCondition pc) {
		
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf eio1 = null;
				EdgeIndexOfChar eio2 = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeIndexOfChar) {
					eio1 = (EdgeIndexOf) e1;
					eio2 = (EdgeIndexOfChar) e2;
				} else if (e2 instanceof EdgeIndexOf && e1 instanceof EdgeIndexOfChar) {
					eio1 = (EdgeIndexOf) e2;
					eio2 = (EdgeIndexOfChar) e1;
				} else
				{ continue; }
				if (!eio1.getDest().isConstant()) {continue;}
				String constant = eio1.getIndex().getExpression().solution();
				
				for (int k = 0; k < constant.length(); k++) {
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant.charAt(k)), Comparator.EQ, eio2.getIndex().getExpression()));
					loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(k), Comparator.NE, eio2.getIndex()));
					pc._addDet(loic);
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIntIndexOfChar (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf2 eio1 = null;
				EdgeIndexOfChar eio2 = null;
				
				if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeIndexOfChar) {
					eio1 = (EdgeIndexOf2) e1;
					eio2 = (EdgeIndexOfChar) e2;
				} else if (e2 instanceof EdgeIndexOf2 && e1 instanceof EdgeIndexOfChar) {
					eio1 = (EdgeIndexOf2) e2;
					eio2 = (EdgeIndexOfChar) e1;
				} else
				{ continue; }
				if (!eio1.getDest().isConstant()) {continue;}
				String constant = eio1.getIndex().getExpression().solution();
				
				for (int k = 0; k < constant.length(); k++) {
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getMinIndex(), Comparator.GE, eio2.getIndex()));
					loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant.charAt(k)), Comparator.EQ, eio2.getIndex().getExpression()));
					loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(k), Comparator.NE, eio2.getIndex()));
					pc._addDet(loic);
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIntIndexOfCharInt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf2 eio1 = null;
				EdgeIndexOfChar2 eio2 = null;
				
				if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeIndexOfChar2) {
					eio1 = (EdgeIndexOf2) e1;
					eio2 = (EdgeIndexOfChar2) e2;
				} else if (e2 instanceof EdgeIndexOf2 && e1 instanceof EdgeIndexOfChar2) {
					eio1 = (EdgeIndexOf2) e2;
					eio2 = (EdgeIndexOfChar2) e1;
				} else
				{ continue; }
				if (!eio1.getDest().isConstant()) {continue;}
				/*System.out.println("[handleIndexOfStrIntIndexOfCharInt] eio1: " + eio1);
				System.out.println("[handleIndexOfStrIntIndexOfCharInt] eio1.getIndex(): " + eio1.getIndex());
				System.out.println("[handleIndexOfStrIntIndexOfCharInt] eio1.getIndex().getExpression(): " + eio1.getIndex().getExpression());*/
				String constant = eio1.getIndex().getExpression().solution();
				
				/*for (int k = 0; k < constant.length(); k++) {
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getMinIndex(), Comparator.GE, eio2.getIndex()));
					loic.addToList(new LinearIntegerConstraint(eio2.getIndex().getMinDist(), Comparator.GE, eio1.getIndex()));
					loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant.charAt(k)), Comparator.EQ, eio2.getIndex().getExpression()));
					loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(k), Comparator.NE, eio2.getIndex()));
					loic.comment = "indexOfStrInt and indexOfCharInt";
					pc._addDet(loic);
				}*/
				for (int k = 0; k < constant.length(); k++) {
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant.charAt(k)), Comparator.EQ, eio2.getIndex().getExpression()));
					loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(k), Comparator.NE, eio2.getIndex()));
					loic.comment = "indexOfStrInt and indexOfCharInt";
					if (!pc.hasConstraint(loic)) pc._addDet(loic);
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIndexOfCharInt (StringGraph g, PathCondition pc) {	
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf eio1 = null;
				EdgeIndexOfChar2 eio2 = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeIndexOfChar2) {
					eio1 = (EdgeIndexOf) e1;
					eio2 = (EdgeIndexOfChar2) e2;
				} else if (e2 instanceof EdgeIndexOf && e1 instanceof EdgeIndexOfChar2) {
					eio1 = (EdgeIndexOf) e2;
					eio2 = (EdgeIndexOfChar2) e1;
				} else
				{ continue; }
				if (!eio1.getDest().isConstant()) {continue;}
				String constant = eio1.getIndex().getExpression().solution();
				
				for (int k = 0; k < constant.length(); k++) {
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eio2.getIndex().getMinDist(), Comparator.GE, eio1.getIndex()));
					loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant.charAt(k)), Comparator.EQ, eio2.getIndex().getExpression()));
					loic.addToList(new LinearIntegerConstraint(eio1.getIndex()._plus(k), Comparator.NE, eio2.getIndex()));
					loic.comment = "indexOfStr and indexOfCharInt";
					pc._addDet(loic);
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharDependencies (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				if (!(e1 instanceof EdgeIndexOfChar && e2 instanceof EdgeIndexOfChar)) { continue; }
				
				EdgeIndexOfChar eio1 = (EdgeIndexOfChar) e1;
				EdgeIndexOfChar eio2 = (EdgeIndexOfChar) e2;
				
				//if (e1.getDest().equals(e2.getDest())) {
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getExpression(), Comparator.NE, eio2.getIndex().getExpression()));
				loic.addToList(new LinearIntegerConstraint(eio1.sioi, Comparator.EQ, eio2.sioi));
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eio1.sioi, Comparator.NE, eio2.sioi));
				loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getExpression(), Comparator.EQ, eio2.getIndex().getExpression()));
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfCharIndexOfCharInt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOfChar eio1 = null;
				EdgeIndexOfChar2 eio2 = null;
				
				if (e1 instanceof EdgeIndexOfChar && e2 instanceof EdgeIndexOfChar2) {
					eio1 = (EdgeIndexOfChar) e1;
					eio2 = (EdgeIndexOfChar2) e2;
				} else if (e1 instanceof EdgeIndexOfChar2 && e2 instanceof EdgeIndexOfChar) {
					eio2 = (EdgeIndexOfChar2) e1;
					eio1 = (EdgeIndexOfChar) e2;
				}
				else
				{ continue; }
				
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eio2.getIndex().getMinDist(), Comparator.GE, eio1.getIndex()));
				loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getExpression(), Comparator.NE, eio2.getIndex().getExpression()));
				loic.addToList(new LinearIntegerConstraint(eio1.sioi, Comparator.EQ, eio2.sioi));
				loic.comment = "indexOfChar and indexOfCharInt";
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eio2.getIndex().getMinDist(), Comparator.GE, eio1.getIndex()));
				loic.addToList(new LinearIntegerConstraint(eio1.sioi, Comparator.NE, eio2.sioi));
				loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getExpression(), Comparator.EQ, eio2.getIndex().getExpression()));
				loic.comment = "indexOfChar and indexOfCharInt";
				pc._addDet(loic);
			}
		}
		return true;
	}

	
	private static boolean handleIndexOfCharIntDependencies (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				if (!(e1 instanceof EdgeIndexOfChar2 && e2 instanceof EdgeIndexOfChar2)) { continue; }
				
				EdgeIndexOfChar2 eio1 = (EdgeIndexOfChar2) e1;
				EdgeIndexOfChar2 eio2 = (EdgeIndexOfChar2) e2;
				
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				//TODO: Could just be Greater, instead of GE
				loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getMinDist(), Comparator.GE, eio2.getIndex()));
				loic.addToList(new LinearIntegerConstraint(eio2.getIndex().getMinDist(), Comparator.GE, eio1.getIndex()));
				loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getExpression(), Comparator.NE, eio2.getIndex().getExpression()));
				loic.addToList(new LinearIntegerConstraint(eio1.sioi, Comparator.EQ, eio2.sioi));
				loic.comment = "indexOfCharInt and indexOfCharInt";
				pc._addDet(loic);
				
				loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getMinDist(), Comparator.GE, eio2.getIndex()));
				loic.addToList(new LinearIntegerConstraint(eio2.getIndex().getMinDist(), Comparator.GE, eio1.getIndex()));
				loic.addToList(new LinearIntegerConstraint(eio1.sioi, Comparator.NE, eio2.sioi));
				loic.addToList(new LinearIntegerConstraint(eio1.getIndex().getExpression(), Comparator.EQ, eio2.getIndex().getExpression()));
				loic.comment = "indexOfCharInt and indexOfCharInt";
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrStartsWith (StringGraph g, PathCondition pc) {
		//TODO: Think more of this
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf eio = null;
				EdgeStartsWith esw = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeStartsWith) {
					eio = (EdgeIndexOf) e1;
					esw = (EdgeStartsWith) e2;
				} else if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeIndexOf) {
					eio = (EdgeIndexOf) e2;
					esw = (EdgeStartsWith) e1;
				}
				else { continue; }
				
				if (e1.getDest().equals(e2.getDest())) {
					pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(0));
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = eio.getDest().getSolution();
					String constant2 = esw.getDest().getSolution();
					int indexOf = constant2.indexOf(constant1);
					if (indexOf > -1) {
						pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(indexOf));
					} else {
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(eio.sioi, Comparator.GT,new IntegerConstant(constant2.length() - constant1.length())));
						loic.addToList(new LinearIntegerConstraint(eio.sioi, Comparator.EQ,new IntegerConstant(-1)));
						pc._addDet(loic);
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIntStartsWith (StringGraph g, PathCondition pc) {
		//TODO: Think more of this
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {		
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf2 eio = null;
				EdgeStartsWith esw = null;
				
				if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeStartsWith) {
					eio = (EdgeIndexOf2) e1;
					esw = (EdgeStartsWith) e2;
				} else if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeIndexOf2) {
					eio = (EdgeIndexOf2) e2;
					esw = (EdgeStartsWith) e1;
				}
				else { continue; }
				
				if (e1.getDest().equals(e2.getDest())) {
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinIndex(), Comparator.GT, new IntegerConstant(0)));
					loic.addToList(new  LinearIntegerConstraint(eio.sioi, Comparator.EQ, new IntegerConstant(0)));
					pc._addDet(loic);
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = eio.getDest().getSolution();
					String constant2 = esw.getDest().getSolution();
					int indexOf = constant2.indexOf(constant1);
					if (indexOf > -1) {
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinIndex(), Comparator.GE, new IntegerConstant(indexOf)));
						loic.addToList(new  LinearIntegerConstraint(eio.sioi, Comparator.EQ, new IntegerConstant(indexOf)));
						pc._addDet(loic);
						//pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(indexOf));
					} else {
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(eio.sioi, Comparator.GT,new IntegerConstant(constant2.length() - constant1.length())));
						loic.addToList(new LinearIntegerConstraint(eio.sioi, Comparator.EQ,new IntegerConstant(-1)));
						pc._addDet(loic);
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrNotContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {	
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf eio = null;
				EdgeNotContains enc = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeNotContains) {
					eio = (EdgeIndexOf) e1;
					enc = (EdgeNotContains) e2;
				} else if (e1 instanceof EdgeNotContains && e2 instanceof EdgeIndexOf) {
					eio = (EdgeIndexOf) e2;
					enc = (EdgeNotContains) e1;
				}
				else { continue; }
				
				if (e1.getDest().equals(e2.getDest())) {
					pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(-1));
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = eio.getDest().getSolution();
					String constant2 = enc.getDest().getSolution();
					boolean contains = constant2.contains(constant1);
					if (contains) {
						pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(-1));
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIntNotContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {	
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf2 eio = null;
				EdgeNotContains enc = null;
				
				if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeNotContains) {
					eio = (EdgeIndexOf2) e1;
					enc = (EdgeNotContains) e2;
				} else if (e1 instanceof EdgeNotContains && e2 instanceof EdgeIndexOf2) {
					eio = (EdgeIndexOf2) e2;
					enc = (EdgeNotContains) e1;
				}
				else { continue; }
				
				if (e1.getDest().equals(e2.getDest())) {
					pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(-1));
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = eio.getDest().getSolution();
					String constant2 = enc.getDest().getSolution();
					boolean contains = constant2.contains(constant1);
					if (contains) {
						pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(-1));
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrNotStartsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {	
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf eio = null;
				EdgeNotStartsWith enc = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeNotStartsWith) {
					eio = (EdgeIndexOf) e1;
					enc = (EdgeNotStartsWith) e2;
				} else if (e1 instanceof EdgeNotStartsWith && e2 instanceof EdgeIndexOf) {
					eio = (EdgeIndexOf) e2;
					enc = (EdgeNotStartsWith) e1;
				}
				else { continue; }
				
				if (e1.getDest().equals(e2.getDest())) {
					pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(-1));
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = eio.getDest().getSolution();
					String constant2 = enc.getDest().getSolution();
					boolean startswith = constant2.startsWith(constant1);
					if (startswith) {
						pc._addDet(Comparator.EQ, eio.sioi, new IntegerConstant(-1));
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIntNotStartsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {	
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf2 eio = null;
				EdgeNotStartsWith enc = null;
				
				if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeNotStartsWith) {
					eio = (EdgeIndexOf2) e1;
					enc = (EdgeNotStartsWith) e2;
				} else if (e1 instanceof EdgeNotStartsWith && e2 instanceof EdgeIndexOf2) {
					eio = (EdgeIndexOf2) e2;
					enc = (EdgeNotStartsWith) e1;
				}
				else { continue; }
				
				if (e1.getDest().equals(e2.getDest())) {
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinIndex(), Comparator.GT, new IntegerConstant(0)));
					loic.addToList(new LinearIntegerConstraint(eio.sioi, Comparator.EQ, new IntegerConstant(-1)));
					pc._addDet(loic);
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = eio.getDest().getSolution();
					String constant2 = enc.getDest().getSolution();
					boolean startswith = constant2.startsWith(constant1);
					if (startswith) {
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinIndex(), Comparator.GT, new IntegerConstant(0)));
						loic.addToList(new LinearIntegerConstraint(eio.sioi, Comparator.EQ, new IntegerConstant(-1)));
						pc._addDet(loic);
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {	
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf eio = null;
				EdgeContains enc = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeContains) {
					eio = (EdgeIndexOf) e1;
					enc = (EdgeContains) e2;
				} else if (e1 instanceof EdgeContains && e2 instanceof EdgeIndexOf) {
					eio = (EdgeIndexOf) e2;
					enc = (EdgeContains) e1;
				}
				else { continue; }
				
				if (e1.getDest().equals(e2.getDest())) {
					pc._addDet(Comparator.GE, eio.sioi, new IntegerConstant(0));
				}
				else {
					if (!(e1.getDest().isConstant() && e2.getDest().isConstant())) { continue; }
					String constant1 = eio.getDest().getSolution();
					String constant2 = enc.getDest().getSolution();
					boolean contains = constant2.contains(constant1);
					if (contains) {
						pc._addDet(Comparator.GE, eio.sioi, new IntegerConstant(0));
					}
				}
			}
		}
		return true;
	}
	
	
	private static boolean handleIndexOfStrCharAt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {	
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf eio = null;
				EdgeCharAt eca = null;
				
				if (e1 instanceof EdgeIndexOf && e2 instanceof EdgeCharAt) {
					eio = (EdgeIndexOf) e1;
					eca = (EdgeCharAt) e2;
				} else if (e1 instanceof EdgeCharAt && e2 instanceof EdgeIndexOf) {
					eio = (EdgeIndexOf) e2;
					eca = (EdgeCharAt) e1;
				}
				else { continue; }
				
				if (!(eio.getDest().isConstant())) { continue; }
				String constant1 = eio.getDest().getSolution();
				//TODO: mmm...
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.LT, eio.sioi));
				loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.GE, eio.sioi._plus(constant1.length())));
				for (int k = 0; k < constant1.length(); k++) {
					char character = constant1.charAt(k);
					loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(character)));
				}
				pc._addDet(loic);
			}
		}
		return true;
	}
	
	private static boolean handleIndexOfStrIntCharAt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size() - 1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {	
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (!sameSource(e1,e2)) {continue;}
				
				EdgeIndexOf2 eio = null;
				EdgeCharAt eca = null;
				
				if (e1 instanceof EdgeIndexOf2 && e2 instanceof EdgeCharAt) {
					eio = (EdgeIndexOf2) e1;
					eca = (EdgeCharAt) e2;
				} else if (e1 instanceof EdgeCharAt && e2 instanceof EdgeIndexOf2) {
					eio = (EdgeIndexOf2) e2;
					eca = (EdgeCharAt) e1;
				}
				else { continue; }
				
				if (!(eio.getDest().isConstant())) { continue; }
				String constant1 = eio.getDest().getSolution();
				//TODO: mmm...
				/*LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.LT, eio.sioi));
				loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.GE, eio.sioi._plus(constant1.length())));
				for (int k = 0; k < constant1.length(); k++) {
					char character = constant1.charAt(k);
					loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(character)));
				}*/
				
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(new IntegerConstant((int) constant1.charAt(0)), Comparator.EQ, eca.getValue()) );
				loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, eca.getIndex()));
				loic.comment = "indexOfStrInt and charAt";
				pc._addDet(loic);
				
				//TODO: Remove
				if (scg.isSatisfiable(pc)) {
					scg.solve(pc);
					PathCondition.flagSolved = true;
				} else {
					return false;
				}
				
				char character = (char) eca.getValue().solution();
				int indexOf = constant1.indexOf(String.valueOf(character));
				if (indexOf > -1) {
					//throw new RuntimeException("reached");
					loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eca.getIndex(), Comparator.LT, eio.getIndex().getMinIndex()));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE,new IntegerConstant(-1)));
					loic.comment = "indexOfStrInt and charAt";
					pc._addDet(loic);
				}
			}
		}
		return true;
	}
	
	
	private static boolean handleBasicIndexOf (StringGraph g, PathCondition pc) {
		if (!handleBasicIndexOfStr(g, pc)) {
			//println ("handleBasicIndexOfStr returned false");
			return false;		
		}
		if (!handleBasicIndexOfStrInt(g, pc)) {
			//println ("handleBasicIndexOfStrInt returned false");
			return false;		
		}
		if (!handleBasicIndexOfChar(g, pc)) {
			//println ("handleBasicIndexOfChar returned false");
			return false;		
		}
		if (!handleBasicIndexOfCharInt(g, pc)) {
			//println ("handleBasicIndexOfCharInt returned false");
			return false;		
		}
		return true;
	}
	
	private static boolean handleBasicLastIndexOf (StringGraph g, PathCondition pc) {
		if (!handleBasicLastIndexOfChar(g, pc)) {
			//println ("handleBasicIndexOfChar returned false");
			return false;		
		}
		if (!handleBasicLastIndexOfCharInt(g, pc)) {
			//println ("handleBasicIndexOfChar returned false");
			return false;		
		}
		return true;
	}
	
	private static boolean handleBasicIndexOfStr (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeIndexOf)) { continue; }
			EdgeIndexOf eio = (EdgeIndexOf) e;
			pc._addDet(Comparator.GE, eio.getSource().getSymbolicLength(), eio.getDest().getSymbolicLength()._plus(eio.getIndex()));
		}
		return true;
	}
	
	private static boolean handleBasicIndexOfStrInt (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeIndexOf2)) { continue; }
			EdgeIndexOf2 eio = (EdgeIndexOf2) e;
			/*LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.GE, eio.getIndex().getMinIndex()));
			loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
			loic.comment = "indexOfStrInt basic";
			pc._addDet(loic);*/
			
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
			
			pc._addDet(Comparator.GE, eio.getSource().getSymbolicLength(), eio.getDest().getSymbolicLength()._plus(eio.getIndex()));
		}
		return true;
	}
	
	private static boolean handleBasicIndexOfChar (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeIndexOfChar)) { continue; }
			EdgeIndexOfChar eio = (EdgeIndexOfChar) e;
			pc._addDet(Comparator.GE, eio.getSource().getSymbolicLength(), eio.getIndex()._plus(1));
		}
		return true;
	}
	
	private static boolean handleBasicLastIndexOfChar (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeLastIndexOfChar)) { continue; }
			EdgeLastIndexOfChar eio = (EdgeLastIndexOfChar) e;
			pc._addDet(Comparator.GE, eio.getSource().getSymbolicLength(), eio.getIndex()._plus(1));
		}
		return true;
	}
	
	private static boolean handleBasicLastIndexOfCharInt (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeLastIndexOfChar2)) { continue; }
			EdgeLastIndexOfChar2 eio = (EdgeLastIndexOfChar2) e;
			pc._addDet(Comparator.GE, eio.getSource().getSymbolicLength(), eio.getIndex()._plus(1));
			LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			loic.addToList(new LinearIntegerConstraint(eio.getIndex(),Comparator.LE, eio.getIndex().getMinDist()));
			loic.addToList(new LinearIntegerConstraint(eio.getIndex(),Comparator.EQ, new IntegerConstant(-1)));
			pc._addDet(loic);
		}
		return true;
	}
	
	private static boolean handleBasicIndexOfCharInt (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeIndexOfChar2)) { continue; }
			EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e;
			/*LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.GE, eio.getIndex().getMinDist()));
			loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
			loic.comment ="indexOfCharInt basic";
			pc._addDet(loic);*/
			
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
			
			pc._addDet(Comparator.GE, eio.getSource().getSymbolicLength(), eio.getIndex()._plus(1));
		}
		return true;
	}
	
	private static boolean handleBooleanConstraints (StringGraph g, PathCondition pc) {
		 if (!handleBasicBooleanConstraints(g, pc)) {
			 logger.info ("handleBasicBooleanConstraints returned false");
			 return false;
		 }
		 if (!handleStartsWith (g, pc)) {
			 logger.info ("handleStartsWith returned false");
			 return false;
		 }
		 if (!handleEndsWith (g, pc)) {
			 logger.info ("handleStartsWith returned false");
			 return false;
		 }
		 if (!handleContains (g, pc)) {
			 logger.info ("handleContains returned false");
			 return false;
		 }
		 if (!handleStartsWithContains (g, pc)) {
			 logger.info ("handleStartsWithContains returned false");
			 return false;
		 }
		 if (!handleEndsWithContains (g, pc)) {
			 logger.info ("handleEndsWithContains returned false");
			 return false;
		 }
		 //TODO: Test
		 if (!handleEndsWithCharAt(g, pc)) {
			 logger.info ("handleEndsWithContains returned false");
			 return false;
		 }
		 return true;
	}
	
	private static boolean handleEndsWithCharAt (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				EdgeEndsWith eew = null;
				EdgeCharAt eca = null;
				if (e1 instanceof EdgeEndsWith && e2 instanceof EdgeCharAt) {
					eew = (EdgeEndsWith) e1;
					eca = (EdgeCharAt) e2;
				} else if (e2 instanceof EdgeEndsWith && e1 instanceof EdgeCharAt) {
					eew = (EdgeEndsWith) e2;
					eca = (EdgeCharAt) e1;
				} else {
					continue;
				}
				
				if (eew.getDest().isConstant()) {
					String solution = e1.getDest().getSolution();
					for (int k = 0; k < solution.length(); k++) {
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.NE, eew.getSource().getSymbolicLength()._minus(solution.length() - k)));
						loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(solution.charAt(k))));
						pc._addDet(loic);
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleBasicBooleanConstraints (StringGraph g, PathCondition pc) {
		 if (!handleBasicStartsWith (g, pc)) {
			 logger.info ("handleBasicStartsWith returned false");
			 return false;
		 }
		 if (!handleBasicEndsWith (g, pc)) {
			 logger.info ("handleBasicEndsWith returned false");
			 return false;
		 }
		 if (!handleBasicContains (g, pc)) {
			 logger.info ("handleBasicContains returned false");
			 return false;
		 }
		 return true;
	}
	
	private static boolean handleBasicStartsWith (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (e instanceof EdgeStartsWith) {
				pc._addDet(Comparator.GE, e.getSource().getSymbolicLength(), e.getDest().getSymbolicLength());
			}
		}
		return true;
	}
	
	private static boolean handleBasicEndsWith (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (e instanceof EdgeEndsWith) {
				pc._addDet(Comparator.GE, e.getSource().getSymbolicLength(), e.getDest().getSymbolicLength());
			}
		}
		return true;
	}
	
	private static boolean handleBasicContains (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (e instanceof EdgeContains) {
				pc._addDet(Comparator.GE, e.getSource().getSymbolicLength(), e.getDest().getSymbolicLength());
			}
		}
		return true;
	}
	
	private static boolean handleConcat (StringGraph g, PathCondition pc) {
		if (!handleConcatBasic1(g, pc)) {
			//println ("!handleConcatBasic returned false");
			return false;
		}
		if (!handleConcatBasic2(g, pc)) {
			//println ("!handleConcatBasic returned false");
			return false;
		}
		return true;
	}
	
	private static boolean handleConcatBasic1 (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (e instanceof EdgeConcat) {
				if (e.getDest().isConstant()) {
					String destString = e.getDest().getSolution();
					if (e.getSources().get(0).isConstant() && e.getSources().get(1).isConstant()) {
						//All is constant
						String leftString = e.getSources().get(0).getSolution();
						String rightString = e.getSources().get(1).getSolution();
						if (!leftString.concat(rightString).equals(destString)) {
							return false;
						}
					}
					else if (e.getSources().get(0).isConstant()) {
						//"a".concat(a) == "ab"
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
						//a.concat("b") == "ab"
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
						//"a".concat("b") == c
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
		return true;
	}
	
	private static boolean handleConcatBasic2 (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (e instanceof EdgeConcat) {
				pc._addDet (Comparator.EQ, e.getSources().get(0).getSymbolicLength()._plus(e.getSources().get(1).getSymbolicLength()), e.getDest().getSymbolicLength());
			}
		}
		return true;
	}
	
	/***
	 * Check if a graph has an edge StartsWith and NotStartsWith inbetween the same set
	 * of two vertices. If that is true, then the graph can not be solved.
	 * 
	 * @param g
	 * @param pc
	 * @return
	 */
	private static boolean handleStartsWithContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!sameSource(e1,e2)) continue;
				if (!e1.getDest().equals(e2.getDest())) continue;
				if ((e1 instanceof EdgeStartsWith && e2 instanceof EdgeNotContains) ||
					(e1 instanceof EdgeNotContains && e2 instanceof EdgeStartsWith)) {
						return false;
				}
				else if ((e1 instanceof EdgeNotStartsWith && e2 instanceof EdgeContains) ||
						(e1 instanceof EdgeContains && e2 instanceof EdgeNotStartsWith)) {
					return false;
				}
			}
		}
		return true;
	}
	
	/***
	 * Check if a graph has an edge StartsWith and NotStartsWith inbetween the same set
	 * of two vertices. If that is true, then the graph can not be solved.
	 * 
	 * @param g
	 * @param pc
	 * @return
	 */
	private static boolean handleEndsWithContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!sameSource(e1,e2)) continue;
				if (!e1.getDest().equals(e2.getDest())) continue;
				if ((e1 instanceof EdgeEndsWith && e2 instanceof EdgeNotContains) ||
					(e1 instanceof EdgeNotContains && e2 instanceof EdgeEndsWith)) {
						return false;
				}
				else if ((e1 instanceof EdgeNotEndsWith && e2 instanceof EdgeContains) ||
						(e1 instanceof EdgeContains && e2 instanceof EdgeNotEndsWith)) {
					return false;
				}
			}
		}
		return true;
	}
	
	/***
	 * Check if a graph has an edge StartsWith and NotStartsWith inbetween the same set
	 * of two vertices. If that is true, then the graph can not be solved.
	 * 
	 * @param g
	 * @param pc
	 * @return
	 */
	private static boolean handleStartsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!sameSource(e1,e2)) continue;
				if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeStartsWith &&
						e1.getDest().isConstant() && e2.getDest().isConstant()) {
							String e1string = e1.getDest().getSolution();
							String e2string = e2.getDest().getSolution();
							if (!(e1string.contains(e2string) || e2string.contains(e1string))) {
								return false;
							}
				}
				if (!e1.getDest().equals(e2.getDest())) continue;
				if ((e1 instanceof EdgeStartsWith && e2 instanceof EdgeNotStartsWith) ||
					(e1 instanceof EdgeNotStartsWith && e2 instanceof EdgeStartsWith)) {
						return false;
				}
			}
		}
		return true;
	}
	
	/***
	 * Check if a graph has an edge EndsWith and NotEndsWith inbetween the same set
	 * of two vertices. If that is true, then the graph can not be solved.
	 * 
	 * @param g
	 * @param pc
	 * @return
	 */
	private static boolean handleEndsWith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!sameSource(e1,e2)) continue;
				if (e1 instanceof EdgeEndsWith && e2 instanceof EdgeEndsWith &&
						e1.getDest().isConstant() && e2.getDest().isConstant()) {
							String e1string = e1.getDest().getSolution();
							String e2string = e2.getDest().getSolution();
							if (!(e1string.contains(e2string) || e2string.contains(e1string))) {
								return false;
							}
				}

				if (!e1.getDest().equals(e2.getDest())) continue;
				if ((e1 instanceof EdgeEndsWith && e2 instanceof EdgeNotEndsWith) ||
					(e1 instanceof EdgeNotEndsWith && e2 instanceof EdgeEndsWith)) {
						return false;
				}
			}
		}
		return true;
	}
	
	private static boolean handleCharAt (StringGraph g, PathCondition pc) {
		if (!handleCharAtBasics(g, pc)) {
			//println ("handleCharAtBasics returned false");
			return false;
		}
		if (!handleNotCharAtBasics(g, pc)) {
			//println ("handleNotCharAtBasics returned false");
			return false;
		}
		if (!handleCharAtDependencies(g, pc)) {
			//println ("handleCharAtDependencies returned false");
			return false;
		}
		if (!handleCharAtStartswith(g, pc)) {
			//println ("handleCharAtDependencies returned false");
			return false;
		}
		if (!handleCharAtEndswith(g, pc)) {
			//println ("handleCharAtDependencies returned false");
			return false;
		}
		if (!handleCharAtNotContains(g, pc)) {
			//println ("handleCharAtNotContains returned false");
			return false;
		}
		return true;
	}
	
	private static boolean handleCharAtBasics (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeCharAt)) continue;
			EdgeCharAt eca = (EdgeCharAt) e;
			pc._addDet(Comparator.GE, eca.index, new IntegerConstant(0));
			pc._addDet(Comparator.LT, eca.index, new IntegerConstant(MAXIMUM_LENGTH));
			pc._addDet(Comparator.GE, eca.value, new IntegerConstant(SymbolicStringConstraintsGeneral.MIN_CHAR));
			pc._addDet(Comparator.LE, eca.value, new IntegerConstant(SymbolicStringConstraintsGeneral.MAX_CHAR));
			pc._addDet(Comparator.LT, eca.index, e.getSource().getSymbolicLength());
		}
		return true;
	}
	
	private static boolean handleNotCharAtBasics (StringGraph g, PathCondition pc) {
		for (Edge e: g.getEdges()) {
			if (!(e instanceof EdgeNotCharAt)) continue;
			EdgeNotCharAt eca = (EdgeNotCharAt) e;
			pc._addDet(Comparator.GE, eca.index, new IntegerConstant(0));
			pc._addDet(Comparator.LT, eca.index, new IntegerConstant(MAXIMUM_LENGTH));
			pc._addDet(Comparator.GE, eca.value, new IntegerConstant(SymbolicStringConstraintsGeneral.MIN_CHAR));
			pc._addDet(Comparator.LE, eca.value, new IntegerConstant(SymbolicStringConstraintsGeneral.MAX_CHAR));
			pc._addDet(Comparator.LT, eca.index, e.getSource().getSymbolicLength());
		}
		return true;
	}
	
	
	private static boolean handleCharAtEndswith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) {continue;}
				if (!sameSource(e1,e2)) continue;
				EdgeCharAt eca = null;
				EdgeEndsWith esw = null;
				if (e1 instanceof EdgeCharAt && e2 instanceof EdgeEndsWith) {
					eca = (EdgeCharAt) e1;
					esw = (EdgeEndsWith) e2;
				}
				else if (e1 instanceof EdgeEndsWith && e2 instanceof EdgeCharAt) {
					eca = (EdgeCharAt) e2;
					esw = (EdgeEndsWith) e1;
				}
				else {
					continue;
				}
				if (!esw.getDest().isConstant()) {continue;}
				String constantString = esw.getDest().getSolution();
				if (eca.index instanceof IntegerConstant) {
					int index = (int) eca.index.solution();
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.LT, eca.getSource().getSymbolicLength()._minus(constantString.length())));
					loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(constantString.charAt(index))));
				}
				else {
					for (int k = 0; k < constantString.length(); k++) {
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.NE, e1.getSource().getSymbolicLength()._minus(k)));
						loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(constantString.charAt(constantString.length() - k - 1))));
						pc._addDet(loic);
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleCharAtStartswith (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) {continue;}
				if (!sameSource(e1,e2)) continue;
				EdgeCharAt eca = null;
				EdgeStartsWith esw = null;
				if (e1 instanceof EdgeCharAt && e2 instanceof EdgeStartsWith) {
					eca = (EdgeCharAt) e1;
					esw = (EdgeStartsWith) e2;
				}
				else if (e1 instanceof EdgeStartsWith && e2 instanceof EdgeCharAt) {
					eca = (EdgeCharAt) e2;
					esw = (EdgeStartsWith) e1;
				}
				else {
					continue;
				}
				if (!esw.getDest().isConstant()) {continue;}
				String constantString = esw.getDest().getSolution();
				if (eca.index instanceof IntegerConstant) {
					int index = (int) eca.index.solution();
					if (index < constantString.length()) {
						pc._addDet(Comparator.EQ, eca.value, new IntegerConstant(constantString.charAt(index)));
					}
				}
				else {
					for (int k = 0; k < constantString.length(); k++) {
						LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
						loic.addToList(new LinearIntegerConstraint(eca.index, Comparator.NE, new IntegerConstant(k)));
						loic.addToList(new LinearIntegerConstraint(eca.value, Comparator.EQ, new IntegerConstant(constantString.charAt(k))));
						pc._addDet(loic);
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleCharAtNotContains (StringGraph g, PathCondition pc) {
		
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) {continue;}
				if (!sameSource(e1,e2)) continue;
				EdgeCharAt eca = null;
				EdgeNotContains esw = null;
				if (e1 instanceof EdgeCharAt && e2 instanceof EdgeNotContains) {
					eca = (EdgeCharAt) e1;
					esw = (EdgeNotContains) e2;
				}
				else if (e1 instanceof EdgeNotContains && e2 instanceof EdgeCharAt) {
					eca = (EdgeCharAt) e2;
					esw = (EdgeNotContains) e1;
				}
				else {
					continue;
				}
				if (!esw.getDest().isConstant()) {continue;}
				String constantString = esw.getDest().getSolution();
				if (constantString.length() > 1) {continue;}
				char charConstant = constantString.charAt(0);
				pc._addDet(Comparator.NE, eca.value, new IntegerConstant(charConstant));
			}
		}
		return true;
	}
	
	private static boolean handleCharAtDependencies (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) {continue;}
				if (!sameSource(e1,e2)) continue;
				if (!(e1 instanceof EdgeCharAt && e2 instanceof EdgeCharAt)) {continue;}
				EdgeCharAt eca1 = (EdgeCharAt) e1;
				EdgeCharAt eca2 = (EdgeCharAt) e2;
				if (eca1.index instanceof IntegerConstant && eca2.index instanceof IntegerConstant) {
					
					int index1 = (int) ((IntegerConstant) eca1.index).solution();
					int index2 = (int) ((IntegerConstant) eca2.index).solution();
					if (index1 != index2) continue;
					pc._addDet(Comparator.EQ, eca1.value, eca2.value);
				}
			}
		}
		return true;
	}
	
	/***
	 * Check if a graph has an edge Contains and NotContains inbetween the same set
	 * of two vertices. If that is true, then the graph can not be solved.
	 * 
	 * @param g
	 * @param pc
	 * @return
	 */
	private static boolean handleContains (StringGraph g, PathCondition pc) {
		for (int i = 0; i < g.getEdges().size()-1; i++) {
			for (int j = i+1; j < g.getEdges().size(); j++) {
				Edge e1 = g.getEdges().get(i);
				Edge e2 = g.getEdges().get(j);
				if (e1 instanceof EdgeConcat || e2 instanceof EdgeConcat) continue;
				if (!sameSource(e1,e2)) continue;
				if (!e1.getDest().equals(e2.getDest())) continue;
				if ((e1 instanceof EdgeContains && e2 instanceof EdgeNotContains) ||
					(e1 instanceof EdgeNotContains && e2 instanceof EdgeContains)) {
						return false;
				}
			}
		}
		return true;
	}
	
	private static boolean handleEquality (StringGraph g, PathCondition pc) {
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
		return true;
	}
	
	private static boolean handleConstants (StringGraph g, PathCondition pc) {
		ArrayList<Integer> edgesToRemove = new ArrayList<Integer>();
		for (int i = 0; i < g.getEdges().size(); i++) {
			Edge e = g.getEdges().get(i);
			if (!e.allVertecisAreConstant()) {continue;}
			if (e instanceof EdgeNotEqual) {
				EdgeNotEqual edge = (EdgeNotEqual) e;
				String source = edge.getSource().getSolution();
				String dest = edge.getDest().getSolution();
				if (source.equals(dest)) {
					return false;
				}
				edgesToRemove.add(i); //Remove constant edge afterwards
			}
			else if (e instanceof EdgeStartsWith) {
				EdgeStartsWith edge = (EdgeStartsWith) e;
				String source = edge.getSource().getSolution();
				String dest = edge.getDest().getSolution();
				if (!source.startsWith(dest)) {
					return false;
				}
				edgesToRemove.add(i); //Remove constant edge afterwards
			}
			else if (e instanceof EdgeNotStartsWith) {
				EdgeNotStartsWith edge = (EdgeNotStartsWith) e;
				String source = edge.getSource().getSolution();
				String dest = edge.getDest().getSolution();
				if (source.startsWith(dest)) {
					return false;
				}
				edgesToRemove.add(i); //Remove constant edge afterwards
			}
			else if (e instanceof EdgeEndsWith) {
				EdgeEndsWith edge = (EdgeEndsWith) e;
				String source = edge.getSource().getSolution();
				String dest = edge.getDest().getSolution();
				if (!source.endsWith(dest)) {
					return false;
				}
				edgesToRemove.add(i); //Remove constant edge afterwards
			}
			else if (e instanceof EdgeNotEndsWith) {
				EdgeNotEndsWith edge = (EdgeNotEndsWith) e;
				String source = edge.getSource().getSolution();
				String dest = edge.getDest().getSolution();
				if (source.endsWith(dest)) {
					return false;
				}
				edgesToRemove.add(i); //Remove constant edge afterwards
			}
			else if (e instanceof EdgeContains) {
				EdgeContains edge = (EdgeContains) e;
				String source = edge.getSource().getSolution();
				String dest = edge.getDest().getSolution();
				if (!source.contains(dest)) {
					return false;
				}
				edgesToRemove.add(i); //Remove constant edge afterwards
			}
			else if (e instanceof EdgeNotContains) {
				EdgeNotContains edge = (EdgeNotContains) e;
				String source = edge.getSource().getSolution();
				String dest = edge.getDest().getSolution();
				if (source.contains(dest)) {
					return false;
				}
				edgesToRemove.add(i); //Remove constant edge afterwards
			}
			else if (e instanceof EdgeConcat) {
				EdgeConcat edge = (EdgeConcat) e;
				String source1 = edge.getSources().get(0).getSolution();
				String source2 = edge.getSources().get(1).getSolution();
				String dest = edge.getDest().getSolution();
				if (!source1.concat(source2).equals(dest)) {
					return false;
				}
				edgesToRemove.add(i); //Remove constant edge afterwards
			}
		}
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
	
	private static boolean sameSource (Edge e1, Edge e2) {
		if (e1.isHyper() || e2.isHyper()) return false;
		return e1.getSource().equals(e2.getSource());
	}
	
}

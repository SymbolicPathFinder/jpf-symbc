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

package gov.nasa.jpf.symbc.string;

// updated by Lucas?
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
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
import gov.nasa.jpf.symbc.string.graph.EdgeLastIndexOf2;
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
import gov.nasa.jpf.symbc.string.graph.PreProcessGraph;
import gov.nasa.jpf.symbc.string.graph.StringGraph;
import gov.nasa.jpf.symbc.string.graph.Vertex;
import gov.nasa.jpf.symbc.string.translate.TranslateToAutomata;
import gov.nasa.jpf.symbc.string.translate.TranslateToAutomataSpeedUp;
import gov.nasa.jpf.symbc.string.translate.TranslateToCVC;
import gov.nasa.jpf.symbc.string.translate.TranslateToCVCInc;
import gov.nasa.jpf.symbc.string.translate.TranslateToSAT;
import gov.nasa.jpf.util.LogManager;
import java.util.logging.Logger;

/**
 * Main entry point for the symbolic string solver.
 * 
 * The solving is split into six steps
 * 
 * 1. Convert the constraints to a StringGraph (what this class does)
 * 2. Preprocess the StringGraph (gov.nasa.jpf.symbc.string.graph.PreProcessGraph
 * 3. Solve the integer constriants (only choco for now)
 * 4. Solve the string constriants with automata/sat/cvc
 * 5. if step 4 gives unsat, and there is more integer values that satisfy step 3, go to step 3
 * 6. Translate the StringGraph to the original symbolic strings.
 * 
 * More info, visit www.cs.sun.ac.za/~gredelinghuys/string
 * 
 * @author GJ Redelinghuys
 *
 */
public class SymbolicStringConstraintsGeneralToText {

	/* Useless from now on */
  static Logger logger = LogManager.getLogger("stringsolver");
	
	/* When creating constant strings, this is used as unique id */
	private static int constantStringCount;
	
	/*The graph representing the current constraints */
	private StringGraph global_graph;
	
	/*The current constraints */
	private StringPathCondition global_spc;
	
	/*Used to generate unique symbolic integers */
	private static SymbolicIntegerGenerator symbolicIntegerGenerator;
	
	/*Set the region of characters to use */
	public static final int MIN_CHAR = 32;
	public static final int MAX_CHAR = 123; //Excluded
	public static final int DIFF_CHAR = MAX_CHAR - MIN_CHAR;
	
	/*Possible sovlers for now */
	public static final String AUTOMATA = "Automata";
	public static final String SAT = "Sat";
	public static final String CVC = "CVC";
	public static final String CVC_INC = "CVC_Inc";
	
	/* Default solver */
	public static String solver = AUTOMATA;
	
	/* Map of the solutions */
	private static Set<StringSymbolic> setOfSolution;
	
	public SymbolicStringConstraintsGeneralToText () {
		
	}
	
	private Vertex createVertex (StringExpression se) {
		Vertex v = new Vertex (se.getName(), symbolicIntegerGenerator);
		global_spc.getNpc()._addDet(Comparator.EQ, v.getSymbolicLength(), se._length());
		return v;
	}
	
	private Vertex createVertex (StringExpression se, int length) {
		Vertex v = new Vertex (se.getName(), length);
		global_spc.getNpc()._addDet(Comparator.EQ, v.getSymbolicLength(), se._length());
		return v;
	}
	
	/**
	 * Converts an expression to a subgraph, the subgraph will be
	 * added to the main graph later.
	 * 
	 * @param se
	 * @return
	 */
	private StringGraph convertToGraph (StringExpression se) {
		StringGraph result = new StringGraph();
		if (se instanceof StringConstant) {
			result = new StringGraph();
			result.addConstantVertex(se.getName(), se.solution());
			constantStringCount++;
		}
		else if (se instanceof StringSymbolic) {
			StringSymbolic temp = (StringSymbolic) se;
			Vertex v = createVertex (temp);
			v.setRepresent(temp);
			result.addVertex (v);
			
		}
		else if (se instanceof DerivedStringExpression) {
			DerivedStringExpression temp = (DerivedStringExpression) se;
			StringGraph graphBefore, graphLeft, graphRight;
			Vertex v1,v2,v3;
			int a1, a2;
			Edge e;

			switch (temp.op) {
			case TRIM:
				graphBefore = convertToGraph(temp.right);
				v1 = createVertex (temp.right);
				v2 = createVertex (temp);
				graphBefore.addVertex (v1);
				graphBefore.addEdge(v1, v2, new EdgeTrimEqual("EdgeTrimEqual_" + v1.getName() + "=" + temp.getName(), v1, v2));
				result = graphBefore;
				break;
			case SUBSTRING:
				// something is symbolic so ...
				graphBefore = convertToGraph((StringExpression) temp.oprlist[0]);
				v1 = createVertex (((StringExpression) temp.oprlist[0]));
				if (temp.oprlist[1] instanceof IntegerConstant && (temp.oprlist.length == 2 || temp.oprlist[2] instanceof IntegerConstant)) {
					a1 = ((IntegerConstant) temp.oprlist[1]).solutionInt();
					a2 = -1;
					if (temp.oprlist.length == 3) {
						a2 = ((IntegerConstant) temp.oprlist[2]).solutionInt();
						//a1 > a2 ????
						v2 = createVertex (temp, a1 - a2);
						//println ("[convertToGraph, SUBSTRING] a1 = " + a1 + ", a2 = " + a2);
						graphBefore.addEdge(v1, v2, new EdgeSubstring2Equal("EdgeSubstring2Equal_" + v1.getName() + "_" + v2.getName() + "_(" + a2+ "," + a1 +")", a2, a1, v1, v2));
					}
					else {
						v2 = createVertex (temp);
						global_spc.getNpc()._addDet(Comparator.EQ, v2.getSymbolicLength(), v1.getSymbolicLength()._minus(a1));
						graphBefore.addEdge(v1, v2, new EdgeSubstring1Equal("EdgeSubstring1Equal_" + v1.getName() + "_" + v2.getName() + "_(" + a1 + ")", a1, v1, v2));
					}
				}
				else if (temp.oprlist[1] instanceof IntegerExpression && temp.oprlist.length == 2) {
					//throw new RuntimeException ("Reached");
					v2 = createVertex (temp);
					IntegerExpression ie = (IntegerExpression) temp.oprlist[1];
					//throw new RuntimeException (ie.getClass().toString());
					processIntegerConstraint(ie);
					global_spc.getNpc()._addDet(Comparator.EQ, v2.getSymbolicLength(), v1.getSymbolicLength()._minus(ie));
					graphBefore.addEdge(v1, v2, new EdgeSubstring1Equal("EdgeSubstring1Equal_" + v1.getName() + "_" + v2.getName() + "_(" + ie.toString() + ")", ie, v1, v2));
					
				}
				else {
					//System.err.println ("Substring with symbolic integers not yet supported");
					if (temp.oprlist[1] instanceof IntegerExpression && temp.oprlist.length == 3 && temp.oprlist[2] instanceof IntegerConstant) {
						v2 = createVertex (temp);
						IntegerExpression ie_a2 = (IntegerExpression) temp.oprlist[1];
						a1 = ((IntegerConstant) temp.oprlist[2]).solutionInt();
						global_spc.getNpc()._addDet(Comparator.EQ, v2.getSymbolicLength(), ie_a2._minus(a1));
						graphBefore.addEdge(v1, v2, new EdgeSubstring2Equal("EdgeSubstring2Equal_" + v1.getName() + "_" + v2.getName() + "_(" + ie_a2+ "," + a1 +")", a1, ie_a2, v1, v2));
					}
					else {
						throw new RuntimeException("Substring with symbolic integers not yet supported");
					}
					
				}
				result = graphBefore;
				break;
			case CONCAT:
				graphLeft = convertToGraph((StringExpression) temp.left);
				graphRight = convertToGraph ((StringExpression) temp.right);
				result.mergeIn(graphLeft);
				result.mergeIn(graphRight);
				v1 = result.findVertex(((StringExpression) temp.left).getName());
				v2 = result.findVertex(((StringExpression) temp.right).getName());
				//println ("[convertToAutomaton] [CONCAT] v1: " + v1.getName() + ", v2: " + v2.getName());
				v3 = createVertex (se);
				e = new EdgeConcat(v3.getName(), v1, v2, v3);
				result.addEdge(v1, v2, v3, (EdgeConcat) e);
				break;
			default:
				//println ("[WARNING] [convertToAutomaton] Did not understand " + temp.op);
			}
		}
		return result;
	}

	/**
	 * Main entry point, solves (not only tests satisfiability) the given
	 * path condition
	 *  
	 * @param pc
	 * @return
	 */
	public boolean isSatisfiable(StringPathCondition pc) {
		//println ("[isSatisfiable] String PC: " + pc.header);
		String string_dp[] = SymbolicInstructionFactory.string_dp;
		/* Set up solver */
		if (string_dp[0].equals("automata")) {
			solver = AUTOMATA;
		}
		else if (string_dp[0].equals("sat")) {
			solver = SAT;
		}
		else if (string_dp[0].equals("cvc")) {
			solver = CVC;
		}
		else if (string_dp[0].equals("cvc_inc")) {
			solver = CVC_INC;
		}
		else {
			/* No solver, return true */
			//println ("[isSatisfiable] No Solver");
			return true;
		}
		setOfSolution = new HashSet<StringSymbolic>();
		StringConstraint sc;
		if (pc == null) {
			//println ("[isSatisfiable] PC is null");
			return true;
		}
		else {sc = pc.header;}
		//if (sc == null) {return true;}
		this.global_spc = pc;
		constantStringCount++;
		if (symbolicIntegerGenerator == null)
			symbolicIntegerGenerator = new SymbolicIntegerGenerator();
		
		global_graph = new StringGraph();
		
		/* Convert each clause in the path condition to a subgraph,
		 * and add it to the global_graph
		 */
		if (sc != null) {
			boolean result = process (sc);
			sc = sc.and;
			while (result == true && sc != null) {
				result = process (sc);
				sc = sc.and;
			}
		}
		
		/* Walk through integer constraints and convert each constraint
		 * to a subgraph and add it to the global_graph
		 */
		
		Constraint constraint = pc.getNpc().header;
		//println ("[isSatisfiable] Int cons given:" + pc.npc.header);
		while (constraint != null) {
			//First solve any previous integer constriants
			
			
			processIntegerConstraint(constraint.getLeft());
			processIntegerConstraint(constraint.getRight());
			constraint = constraint.getTail();
		}
		
		//First solve any previous integer constriants
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		scg.solve(pc.getNpc());
		PathCondition.flagSolved = true;
		
		
		//Start solving
		//println(global_graph.toDot());
		/* Preprocess the graph */
		boolean resultOfPp = PreProcessGraph.preprocess(global_graph, pc.getNpc());
		if (!resultOfPp) {
			//println ("[isSat] Preprocessor gave Unsat");
			return false;
		}
		logger.info(global_graph.toPlainText());
		if (pc.getNpc().header != null) {
			logger.info ("\nvvv vvv vvv vvv\n");
			System.out.println(pc.getNpc().header);
			System.out.println("\n^^^ ^^^ ^^^ ^^^\n");
		}
		return true;
	}
	
	public static String getSolution () {
		StringBuilder sb = new StringBuilder();
		for (StringSymbolic ss: setOfSolution) {
			sb.append(ss.getName());
			sb.append ('[');
			sb.append(ss.solution());
			sb.append("]\n");
		}
		return sb.toString();
	}
	
	/*
	 * Converts an integer-string constriant to a subgraph, which in turn
	 * is added to global_graph
	 */
	private void processIntegerConstraint (Expression e) {
		if (PathCondition.flagSolved == false) {
			SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
			scg.solve(global_spc.getNpc());
			PathCondition.flagSolved = true;
		}
		if (e instanceof SymbolicCharAtInteger) {
			//foundStringIntegerConstraint = true;
			SymbolicCharAtInteger scai = (SymbolicCharAtInteger) e;
			//println ("[processIntegerConstraint] Found charAt constraint with " + scai.se.getName());
			StringGraph sg = convertToGraph(scai.se);
			global_graph.mergeIn(sg);
			PathCondition.flagSolved = true;
			/*if (!(scai.index instanceof IntegerConstant)) {
				throw new RuntimeException("OOPS! " + scai.index.toString());
			}
			else {
				//println ("[processIntegerConstraint] scai.index.getClass(): " + scai.index.getClass());
			}*/
			Vertex v1 = new Vertex ("CharAt_" + scai.index.solution() + "_" + scai.solution(), String.valueOf((char) scai.solution()), true);
			Vertex v2 = global_graph.findVertex(scai.se.getName());
			global_graph.addEdge(v2, v1, new EdgeCharAt("CharAt_" + scai.index.solution() + "_" + scai.solution(), v2, v1, scai.index, scai));
			
		}
		else if (e instanceof SymbolicIndexOfInteger) {
			SymbolicIndexOfInteger sioi = (SymbolicIndexOfInteger) e;
			//println ("[processIntegerConstraint] Found indexOf constraint with " + sioi.getName());
			StringGraph expression = convertToGraph (sioi.expression);
			StringGraph source = convertToGraph (sioi.source);
			global_graph.mergeIn(expression);
			global_graph.mergeIn(source);
			Vertex v1 = global_graph.findVertex(sioi.expression.getName());
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeIndexOf("EdgeIndexOf_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			PathCondition.flagSolved = true; //TODO: Review			
		}
		else if (e instanceof SymbolicLastIndexOfInteger) {
			SymbolicLastIndexOfInteger sioi = (SymbolicLastIndexOfInteger) e;
			//println ("[processIntegerConstraint] Found indexOf constraint with " + sioi.getName());
			StringGraph expression = convertToGraph (sioi.expression);
			StringGraph source = convertToGraph (sioi.source);
			global_graph.mergeIn(expression);
			global_graph.mergeIn(source);
			Vertex v1 = global_graph.findVertex(sioi.expression.getName());
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeLastIndexOf("EdgeLastIndexOf_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			PathCondition.flagSolved = true; //TODO: Review			
		}
		else if (e instanceof SymbolicLastIndexOf2Integer) {
			SymbolicLastIndexOf2Integer sioi = (SymbolicLastIndexOf2Integer) e;
			//println ("[processIntegerConstraint] Found indexOf2 constraint with " + sioi.getName() + " and min dist: " + sioi.getMinIndex().solution());
			StringGraph expression = convertToGraph (sioi.expression);
			StringGraph source = convertToGraph (sioi.source);
			global_graph.mergeIn(expression);
			global_graph.mergeIn(source);
			Vertex v1 = global_graph.findVertex(sioi.expression.getName());
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeLastIndexOf2("EdgeIndexOf2_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			processIntegerConstraint(sioi.getMinIndex());
			PathCondition.flagSolved = true; //TODO: Review
			
		}
		else if (e instanceof SymbolicLastIndexOfChar2Integer) {
			SymbolicLastIndexOfChar2Integer sioi = (SymbolicLastIndexOfChar2Integer) e;
			//println ("[processIntegerConstraint] Found indexOf (char) constraint with " + sioi.getName());
			StringGraph source = convertToGraph (sioi.source);
			Vertex v1 = new Vertex ("CHAR_" + sioi.getExpression().solution(), symbolicIntegerGenerator);
			global_graph.addVertex(v1);
			global_graph.mergeIn(source);
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeLastIndexOfChar2("EdgeIndexOfChar_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			processIntegerConstraint(sioi.getMinDist());
			PathCondition.flagSolved = true; //TODO: Review
			
		}
		else if (e instanceof SymbolicIndexOfCharInteger) {
			SymbolicIndexOfCharInteger sioi = (SymbolicIndexOfCharInteger) e;
			//println ("[processIntegerConstraint] Found indexOf (char) constraint with " + sioi.getName());
			StringGraph source = convertToGraph (sioi.source);
			Vertex v1;
			if (sioi.getExpression() instanceof IntegerConstant) {
				v1 = new Vertex ("CHAR_" + sioi.getExpression().solution(), String.valueOf ((char) sioi.getExpression().solution()), true);
			}
			else {
				v1 = new Vertex ("CHAR_" + sioi.getExpression().solution(), symbolicIntegerGenerator);
			}
			global_graph.addVertex(v1);
			global_graph.mergeIn(source);
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeIndexOfChar("EdgeIndexOfChar_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			PathCondition.flagSolved = true; //TODO: Review
			
		}
		else if (e instanceof SymbolicLastIndexOfCharInteger) {
			SymbolicLastIndexOfCharInteger sioi = (SymbolicLastIndexOfCharInteger) e;
			//println ("[processIntegerConstraint] Found indexOf (char) constraint with " + sioi.getName());
			StringGraph source = convertToGraph (sioi.source);
			Vertex v1;
			if (sioi.getExpression() instanceof IntegerConstant) {
				v1 = new Vertex ("CHAR_" + sioi.getExpression().solution(), String.valueOf ((char) sioi.getExpression().solution()), true);
			}
			else {
				v1 = new Vertex ("CHAR_" + sioi.getExpression().solution(), symbolicIntegerGenerator);
			}
			global_graph.addVertex(v1);
			global_graph.mergeIn(source);
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeLastIndexOfChar("EdgeIndexOfChar_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			PathCondition.flagSolved = true; //TODO: Review
			
		}
		else if (e instanceof SymbolicIndexOfChar2Integer) {
			SymbolicIndexOfChar2Integer sioi = (SymbolicIndexOfChar2Integer) e;
			//println ("[processIntegerConstraint] Found indexOf (char) constraint with " + sioi.getName());
			StringGraph source = convertToGraph (sioi.source);
			Vertex v1 = new Vertex ("CHAR_" + sioi.getExpression().solution(), symbolicIntegerGenerator);
			global_graph.addVertex(v1);
			global_graph.mergeIn(source);
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeIndexOfChar2("EdgeIndexOfChar_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			processIntegerConstraint(sioi.getMinDist());
			PathCondition.flagSolved = true; //TODO: Review
			
		}
		else if (e instanceof SymbolicIndexOf2Integer) {
			SymbolicIndexOf2Integer sioi = (SymbolicIndexOf2Integer) e;
			//println ("[processIntegerConstraint] Found indexOf2 constraint with " + sioi.getName() + " and min dist: " + sioi.getMinIndex().solution());
			StringGraph expression = convertToGraph (sioi.expression);
			StringGraph source = convertToGraph (sioi.source);
			global_graph.mergeIn(expression);
			global_graph.mergeIn(source);
			Vertex v1 = global_graph.findVertex(sioi.expression.getName());
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeIndexOf2("EdgeIndexOf2_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			processIntegerConstraint(sioi.getMinIndex());
			PathCondition.flagSolved = true; //TODO: Review
			
		}
		else if (e instanceof SymbolicLengthInteger) {
			SymbolicLengthInteger sli = (SymbolicLengthInteger) e;
			//println ("[processIntegerConstraint] Found length constraint with " + sli.getName());
			StringGraph parent = convertToGraph(sli.parent);
			global_graph.mergeIn(parent);
			Vertex v1 = global_graph.findVertex(sli.parent.getName());
			global_spc.getNpc()._addDet(Comparator.EQ, v1.getSymbolicLength(), sli);
		}
		/*else {
			if (e != null) {
				//println ("[processIntegerConstraint] Ignoring: " + e.getClass());
			}
		}*/
	}
	
	/*
	 * Add the current clause/constraint to the global_graph
	 */
	private boolean process (StringConstraint sc) {
		if (sc == null) {return true;}
		StringGraph leftGraph, rightGraph;
		StringExpression se_left = sc.left;
		StringExpression se_right = sc.right;
		Vertex v1, v2;
		switch (sc.comp) {
		case EQUALS:
			leftGraph = convertToGraph (se_left);
			rightGraph = convertToGraph (se_right);			
			global_graph.mergeIn(leftGraph);
			global_graph.mergeIn(rightGraph);
			v1 = global_graph.findVertex(se_left.getName());
			
			v2 = global_graph.findVertex(se_right.getName());
			global_graph.addEdge(v1, v2, new EdgeEqual("EdgeEqual_" + v1.getName() + "=" + v2.getName(), v1, v2));
			break;
		case NOTEQUALS:
			leftGraph = convertToGraph (se_left);
			rightGraph = convertToGraph (se_right);			
			global_graph.mergeIn(leftGraph);
			global_graph.mergeIn(rightGraph);
			v1 = global_graph.findVertex(se_left.getName());
			//println ("[process] should be name: " + se_left.getName());
			v2 = global_graph.findVertex(se_right.getName());
			global_graph.addEdge(v1, v2, new EdgeNotEqual("EdgeNotEqual_" + v1.getName() + "=" + v2.getName(), v1, v2));
			break;
		case STARTSWITH:
			leftGraph = convertToGraph (se_left);
			rightGraph = convertToGraph (se_right);			
			global_graph.mergeIn(leftGraph);
			global_graph.mergeIn(rightGraph);
			v1 = global_graph.findVertex(se_left.getName());
			v2 = global_graph.findVertex(se_right.getName());
			global_graph.addEdge(v1, v2, new EdgeStartsWith("EdgeStartsWith_" + v1.getName() + "=" + v2.getName(), v1, v2));
			break;
		case NOTSTARTSWITH:
			//println ("[process, NOTSTARTSWITH] se_left: " + se_left.toString());
			//println ("[process, NOTSTARTSWITH] se_right: " + se_right.toString());
			leftGraph = convertToGraph (se_left);
			//println ("[process, NOTSTARTSWITH] left Graph: " + leftGraph.toDot() + leftGraph.getVertices());
			rightGraph = convertToGraph (se_right);	
			//println ("[process, NOTSTARTSWITH] right Graph: " + rightGraph.toDot() + rightGraph.getVertices());			
			global_graph.mergeIn(leftGraph);
			global_graph.mergeIn(rightGraph);
			//println ("[process, NOTSTARTSWITH] Trying to find: " + se_left.getName());
			//println ("[process, NOTSTARTSWITH] graph: " + global_graph.toDot());
			
			v1 = global_graph.findVertex(se_left.getName());
			v2 = global_graph.findVertex(se_right.getName());
			//println ("[process, NOTSTARTSWITH] global_graph null? " + (global_graph == null));
			//println ("[process, NOTSTARTSWITH] v1 null? " + (v1 == null));
			//println ("[process, NOTSTARTSWITH] v2 null? " + (v2 == null));			
			global_graph.addEdge(v1, v2, new EdgeNotStartsWith("EdgeNotStartsWith_" + v1.getName() + "=" + v2.getName(), v1, v2));
			break;
		case ENDSWITH:
			leftGraph = convertToGraph (se_left);
			rightGraph = convertToGraph (se_right);			
			global_graph.mergeIn(leftGraph);
			global_graph.mergeIn(rightGraph);
			v1 = global_graph.findVertex(se_left.getName());
			v2 = global_graph.findVertex(se_right.getName());
			global_graph.addEdge(v1, v2, new EdgeEndsWith("EdgeEndsWith_" + v1.getName() + "=" + v2.getName(), v1, v2));
			break;
		case NOTENDSWITH:
			leftGraph = convertToGraph (se_left);
			rightGraph = convertToGraph (se_right);			
			global_graph.mergeIn(leftGraph);
			global_graph.mergeIn(rightGraph);
			v1 = global_graph.findVertex(se_left.getName());
			v2 = global_graph.findVertex(se_right.getName());
			global_graph.addEdge(v1, v2, new EdgeNotEndsWith("EdgeNotEndsWith_" + v1.getName() + "=" + v2.getName(), v1, v2));
			break;
		case CONTAINS:
			leftGraph = convertToGraph (se_left);
			rightGraph = convertToGraph (se_right);			
			global_graph.mergeIn(leftGraph);
			global_graph.mergeIn(rightGraph);
			v1 = global_graph.findVertex(se_left.getName());
			v2 = global_graph.findVertex(se_right.getName());
			global_graph.addEdge(v1, v2, new EdgeContains("EdgeContains_" + v1.getName() + "=" + v2.getName(), v1, v2));
			break;
		case NOTCONTAINS:
			leftGraph = convertToGraph (se_left);
			rightGraph = convertToGraph (se_right);			
			global_graph.mergeIn(leftGraph);
			global_graph.mergeIn(rightGraph);
			v1 = global_graph.findVertex(se_left.getName());
			v2 = global_graph.findVertex(se_right.getName());
			global_graph.addEdge(v1, v2, new EdgeNotContains("EdgeNotContains_" + v1.getName() + "=" + v2.getName(), v1, v2));			
			break;
		default:
			throw new RuntimeException ("Do not understand " + sc.comp);
		}
		
		return true;
	}
	
}

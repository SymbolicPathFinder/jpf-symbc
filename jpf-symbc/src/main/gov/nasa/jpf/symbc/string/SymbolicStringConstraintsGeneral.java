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

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Timer;
import java.util.logging.Logger;

import edu.ucsb.cs.vlab.modelling.Output;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
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
import gov.nasa.jpf.symbc.string.graph.EdgeNotCharAt;
import gov.nasa.jpf.symbc.string.graph.EdgeNotContains;
import gov.nasa.jpf.symbc.string.graph.EdgeNotEndsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeNotEqual;
import gov.nasa.jpf.symbc.string.graph.EdgeNotStartsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeReplaceCharChar;
import gov.nasa.jpf.symbc.string.graph.EdgeStartsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeSubstring1Equal;
import gov.nasa.jpf.symbc.string.graph.EdgeSubstring2Equal;
import gov.nasa.jpf.symbc.string.graph.EdgeTrimEqual;
import gov.nasa.jpf.symbc.string.graph.PreProcessGraph;
import gov.nasa.jpf.symbc.string.graph.StringGraph;
import gov.nasa.jpf.symbc.string.graph.Vertex;
import gov.nasa.jpf.symbc.string.translate.TranslateToABC;
import gov.nasa.jpf.symbc.string.translate.TranslateToAutomata;
import gov.nasa.jpf.symbc.string.translate.TranslateToAutomata2;
import gov.nasa.jpf.symbc.string.translate.TranslateToCVC;
import gov.nasa.jpf.symbc.string.translate.TranslateToCVCInc;
import gov.nasa.jpf.symbc.string.translate.TranslateToSAT;
import gov.nasa.jpf.symbc.string.translate.TranslateToZ3;
import gov.nasa.jpf.symbc.string.translate.TranslateToZ3Inc;
import gov.nasa.jpf.symbc.string.translate.TranslateToZ3str2;
import gov.nasa.jpf.util.LogManager;

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
 * Visit http://www1.sun.ac.za/redmine/projects/jpfbugs/issues to log bugs
 * 
 * @author GJ Redelinghuys
 *
 */
public class SymbolicStringConstraintsGeneral {

	/* Useless from now on */
  static Logger logger = LogManager.getLogger("stringsolver");
	public static int constraintCount = 0;
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
	public static final int MAX_CHAR = 127; //Excluded
	public static final int DIFF_CHAR = MAX_CHAR - MIN_CHAR;
	
	/*Possible sovlers for now */
	public static final String ABC = "ABC";
	public static final String Z3STR2 = "Z3str2";
	public static final String AUTOMATA = "Automata";
	public static final String SAT = "Sat";
	public static final String CVC = "CVC";
	public static final String CVC_INC = "CVC_Inc";
	public static final String Z3 = "Z3";
	public static final String Z3_INC = "Z3_INC";
	public static final String WRAPPER = "WRAPPER"; //automata+z3
	
	/* Default solver */
	public static String solver = AUTOMATA;
	
	/* Map of the solutions */
	private static Set<StringSymbolic> setOfSolution;
	
	/*Something added for research into other solving techniques */
	private static final boolean EJECT_TEXT = false;
	
	/*Timer to be used for timing out*/
	public static Timer timer;
	
	/*Time (in ms) until timeout, zero for no timeout*/
	public static long TIMEOUT = 0;
	
	/*Boolean which is flagged when the timeout has been achieved */
	public static boolean timedOut;
	
	/*Mutex lock on timedOut */
	public static Object mutexTimedOut = new Object();
	
	/*Timing*/
	public static long timeInvoked = 0;
	public static long string_duration = 0;
	public static long int_duration = 0;
	
	public static long entered = 0;
	
	public SymbolicStringConstraintsGeneral () {
		
	}
	
	private Vertex createVertex (StringExpression se) {
		boolean oldValue = PathCondition.flagSolved;
		PathCondition.flagSolved = false;
		String vertexName = se.getName();
		PathCondition.flagSolved = oldValue;
		Vertex v = new Vertex (vertexName, symbolicIntegerGenerator);
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
				//println("SUBSTRING CASE\n");
				// something is symbolic so ...
				graphBefore = convertToGraph((StringExpression) temp.oprlist[0]);
				//v1 = createVertex (((StringExpression) temp.oprlist[0]));
				//System.out.println("v1: " + v1.getName());
				boolean oldState = PathCondition.flagSolved;
				PathCondition.flagSolved = false;
				v1 = graphBefore.findVertex(((StringExpression) temp.oprlist[0]).getName());
				PathCondition.flagSolved = oldState;
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
					processIntegerConstraint(ie, null, null, null);
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
				if (v1 == null) v1 = result.findVertex("C_" + ((StringExpression) temp.left).getName());
				v2 = result.findVertex(((StringExpression) temp.right).getName());
				if (v2 == null) v2 = result.findVertex("C_" + ((StringExpression) temp.right).getName());
				//println ("[convertToAutomaton] [CONCAT] v1: " + v1.getName() + ", v2: " + v2.getName());
				v3 = createVertex (se);
				e = new EdgeConcat(v3.getName(), v1, v2, v3);
				result.addEdge(v1, v2, v3, (EdgeConcat) e);
				break;
			case REPLACE:
				/*graphLeft = convertToGraph((StringExpression) temp.oprlist[1]);
				graphRight = convertToGraph ((StringExpression) temp.oprlist[2]);
				result.mergeIn(graphLeft);
				result.mergeIn(graphRight);*/
				graphBefore = convertToGraph ((StringExpression) temp.oprlist[0]);
				result.mergeIn(graphBefore);
				v1 = result.findVertex(((StringExpression) temp.oprlist[0]).getName());
				v2 = createVertex(temp);
				StringConstant s1 = (StringConstant) temp.oprlist[1];
				StringConstant s2 = (StringConstant) temp.oprlist[2];
				e = new EdgeReplaceCharChar("EdgeReplaceCharChar_" + v1.getName() + "_" + v2.getName() + "_(" + s1 + "," + s2 + ")", v1, v2, s2.solution().charAt(0), s1.solution().charAt(0));
				result.addEdge(v1, v2, e);
				break;
			case VALUEOF:
				/*
				 * I have to restrict myself here just because of DNF->CNF blowup
				 */
				//println("In valueof");
				IntegerExpression ie = (IntegerExpression) temp.oprlist[0];
				boolean oldSetting = PathCondition.flagSolved;
				PathCondition.flagSolved = false;
				v1 = new Vertex (temp.getName(), symbolicIntegerGenerator);
				PathCondition.flagSolved = oldSetting;
				result.addVertex(v1);
				
				//Feeble attempt at log
				
				
				/*Constraint temp1 = new LinearIntegerConstraint(v1.getSymbolicLength(), Comparator.EQ, new IntegerConstant(1));
				Constraint temp2 = new LinearIntegerConstraint(ie, Comparator.GT, new IntegerConstant(-10));
				Constraint temp3 = new LinearIntegerConstraint(ie, Comparator.LT, new IntegerConstant(10));
				temp1.and = temp2;
				temp2.and = temp3;
						
				lolic.addToList((LinearIntegerConstraint)temp1);*/
				global_spc.getNpc()._addDet(Comparator.LE, v1.getSymbolicLength(), 5);
				
				int max = 5;
				
				LogicalORLinearIntegerConstraints lolic;
				
				for (int i = 1; i <= max-1; i++) {
					lolic = new LogicalORLinearIntegerConstraints();
					lolic.addToList(new LinearIntegerConstraint(v1.getSymbolicLength(), Comparator.LE, new IntegerConstant (i)));
					if (i == max-1) {
						//Don't add anything
					} else {
						lolic.addToList(new LinearIntegerConstraint(ie, Comparator.GE, new IntegerConstant ((int) Math.pow(10, i))));
						global_spc.getNpc()._addDet(lolic);
					}
					
					
					lolic = new LogicalORLinearIntegerConstraints();
					lolic.addToList(new LinearIntegerConstraint(v1.getSymbolicLength(), Comparator.LE, new IntegerConstant (i)));
					if (i == 1) {
						lolic.addToList(new LinearIntegerConstraint(ie, Comparator.LE, new IntegerConstant (0)));
					} else {
						lolic.addToList(new LinearIntegerConstraint(ie, Comparator.LE, new IntegerConstant (-1 * ((int) Math.pow(10, i-1)))));
					}
					global_spc.getNpc()._addDet(lolic);
				}
				
				for (int i = 2; i <= max; i++) {
					lolic = new LogicalORLinearIntegerConstraints();
					lolic.addToList(new LinearIntegerConstraint(v1.getSymbolicLength(), Comparator.GE, new IntegerConstant (i)));
					lolic.addToList(new LinearIntegerConstraint(ie, Comparator.LT, new IntegerConstant ((int) Math.pow(10, i-1))));
					global_spc.getNpc()._addDet(lolic);
					
					lolic = new LogicalORLinearIntegerConstraints();
					lolic.addToList(new LinearIntegerConstraint(v1.getSymbolicLength(), Comparator.GE, new IntegerConstant (i)));
					lolic.addToList(new LinearIntegerConstraint(ie, Comparator.GT, new IntegerConstant (-1 * ((int) Math.pow(10, i-1)))));
					global_spc.getNpc()._addDet(lolic);
				}
				
				//global_spc.npc._addDet(lolic);
				result.addVertex(v1);
				
				//throw new RuntimeException("NOT HANDLED YET");
				
				break;
			default:
				//println ("[WARNING] [convertToAutomaton] Did not understand " + temp.op);
			}
		}
		return result;
	}

	public boolean isSatisfiable(StringPathCondition pc) {
		logger.info(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
		if (SymbolicInstructionFactory.debugMode)
			System.out.println("string analysis: " + pc);
		//println ("Path Constraint # " + entered);
		//println ("CURRENT PATH CONSTRAINT:\n");
		//println(pc.toString());
		boolean result = inner_isSatisfiable(pc);
		entered++;
		logger.info("\n");
		return result;
	}
	
	/**
	 * Main entry point, solves (not only tests satisfiability) the given
	 * path condition
	 *  
	 * @param pc
	 * @return
	 */
	private boolean inner_isSatisfiable(StringPathCondition pc) {
		String string_dp[] = SymbolicInstructionFactory.string_dp;
		/* Set up solver */
		if (string_dp[0].equals("automata")) {
			solver = AUTOMATA;
		}
		else if (string_dp[0].equals("z3str2")) {
			solver = Z3STR2;
		}
		else if (string_dp[0].equals("ABC")) {
			solver = ABC;
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
		else if (string_dp[0].equals("z3")) {
			solver = Z3;
		}
		else if (string_dp[0].equals("z3_inc")) {
			solver = Z3_INC;
		} else if (string_dp[0].equals("wrapper")) {
			solver = WRAPPER;
		} else {
			/* No solver, return true */
			//println ("[isSatisfiable] No Solver");
			return true;
		}
		
		logger.info("Using solver: " + solver);

		if(solver.equals(ABC)){
			boolean dpresult = TranslateToABC.isSat(pc);
			constraintCount = constraintCount + 1;
			return dpresult;
		}
		
		else if(solver.equals(Z3STR2)){
			System.out.println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$");
			System.out.println("Calling Z3str2\n");
			final Output dpresult = TranslateToZ3str2.solve(pc);
			constraintCount = constraintCount + 1;
			return dpresult.isSAT();
		}
		
		
		TIMEOUT = SymbolicInstructionFactory.stringTimeout;
		SymbolicStringConstraintsGeneral.timedOut = false;

		if (TIMEOUT > 0) {
			timedOut = false;
			timer = new Timer();
			timer.schedule(new SymbolicStringTimeOut(), TIMEOUT);
		}
		try {
			if (EJECT_TEXT) { /* For research into other solving techniques */
				SymbolicStringConstraintsGeneralToText temp = new SymbolicStringConstraintsGeneralToText();
				cancelTimer();
				return temp.isSatisfiable(pc);
			}
			
			setOfSolution = new HashSet<StringSymbolic>();
			StringConstraint sc;
			if (pc == null) {
				cancelTimer();
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
				/* check if there was a timeout */
				checkTimeOut();
			}

			//println("AFTER PROCESS LOOP:\n");
			//println (global_graph.toDot());

			/* Walk through integer constraints and convert each constraint
			 * to a subgraph and add it to the global_graph
			 */
			
			Constraint constraint = pc.getNpc().header;
			//println ("[isSatisfiable] Int cons given:" + pc.npc.header);
			while (constraint != null) {
				processIntegerConstraint(constraint.getLeft(), constraint.getComparator(), constraint.getRight(), constraint);
				processIntegerConstraint(constraint.getRight(), constraint.getComparator(), constraint.getLeft(), constraint);
				constraint = constraint.getTail();
				//println ("Constraints: " + pc.npc.header + "\nDone");
				/* check if there was a timeout */
				checkTimeOut();
			}
			
			
			//First solve any previous integer constriants
			SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
			scg.solve(pc.getNpc());
			PathCondition.flagSolved = true;

			
			boolean resultOfPp = PreProcessGraph.preprocess(global_graph, pc.getNpc());
			if (!resultOfPp) {
				System.out.println("Preprocessor found unsat");
			}
			
			if (SymbolicInstructionFactory.preprocesOnly) {
				System.out.println("Preprocessoring only");
				return resultOfPp;
			}
			
			//boolean resultOfPp = PreProcessGraphDisabled.preprocess(global_graph, pc.npc);
			//System.out.println("Number of edges after preprocessing: " + global_graph.getEdges().size());
			/* check if there was a timeout */
			checkTimeOut();
			if (!resultOfPp) {
				//println ("[isSat] Preprocessor gave Unsat");
				cancelTimer();
				if (SymbolicInstructionFactory.regressMode) {
					String output = "##STRING PC: (UNSAT) " + pc;
					System.out.println(output);
				}

				return false;
			}
			/* Call the string solver, it will in turn churn away until all
			 * options are exhuasted or a satisfiable solution has turned up
			 */
			boolean decisionProcedure = false;
			try {
				if (solver.equals(SAT)) {
					//println ("[isSatisfiable] Using SAT Solver");
					decisionProcedure = TranslateToSAT.isSat(global_graph, pc.getNpc());
				}
				if (solver.equals(ABC)) {
					logger.info ("[isSatisfiable] Using ABC Solver");
					//decisionProcedure = TranslateToSAT.isSat(global_graph, pc.npc);
					decisionProcedure = false;
				}
				else if (solver.equals(AUTOMATA)) {
					//println ("[isSatisfiable] Using Automata's");
					TranslateToAutomata.duration = 0;
					TranslateToAutomata.int_duration = 0;
					TranslateToAutomata.loops = 0;
					decisionProcedure = TranslateToAutomata2.isSat(global_graph, pc.getNpc());
					timeInvoked++;
				}
				else if (solver.equals(CVC)) {
					//println ("[isSatisfiable] Using Bitvector's");
					decisionProcedure = TranslateToCVC.isSat(global_graph, pc.getNpc()); 
				}
				else if (solver.equals(CVC_INC)) {
					//println ("[isSatisfiable] Using Bitvector's");
					decisionProcedure = TranslateToCVCInc.isSat(global_graph, pc.getNpc()); 
				}
				else if (solver.equals(Z3)) {
					//println ("[isSatisfiable] Using Z3");
					decisionProcedure = TranslateToZ3.isSat(global_graph, pc.getNpc()); 
				}
				else if (solver.equals(Z3_INC)) {
					TranslateToZ3Inc.duration = 0;
					TranslateToZ3Inc.int_duration = 0;
					TranslateToZ3Inc.loops = 0;
					decisionProcedure = TranslateToZ3Inc.isSat(global_graph, pc.getNpc());
					string_duration += TranslateToZ3Inc.duration;
					int_duration += TranslateToZ3Inc.int_duration ;
					//System.out.println("Loops: " + TranslateToZ3Inc.loops);
					timeInvoked++;
				} else if (solver.equals(WRAPPER)) {
					StringGraph cloneGraph = new StringGraph(global_graph);
					PathCondition cloneNpc = pc.getNpc().make_copy();
					boolean pcSolved = PathCondition.flagSolved;
					//start with z3, and swap to automata if something goes wrong
					try {
						decisionProcedure = TranslateToZ3.isSat(global_graph, pc.getNpc());
					} catch (Exception e) {
						logger.info("wrapper-z3 throwed exception; " + e.getMessage());
					} 
					try {
						if (decisionProcedure == false) {
							logger.warning("z3 failed; restoring graph/pc and trying again with automata...");
							global_graph = cloneGraph;
							pc.setNpc(cloneNpc);
							PathCondition.flagSolved = pcSolved;
							
							TranslateToAutomata.duration = 0;
							TranslateToAutomata.int_duration = 0;
							TranslateToAutomata.loops = 0;
							decisionProcedure = TranslateToAutomata2.isSat(
									global_graph, pc.getNpc());
							timeInvoked++;
						}
					} catch (Exception e) {
						logger.severe("wrapper-automata throwed exception; " + e.getMessage());
					}
				}
				else {
					throw new RuntimeException("Unknown string solver!!!");
				}
			} catch (StackOverflowError e) {
				System.err.println("Stacked overflowed");
				e.printStackTrace();
				System.err.println(global_graph.toDot());
			}
			//println ("Done with solvers");
			if (!decisionProcedure) {
				//println ("[isSatisfiable] Decision procedure gave unsat");
				cancelTimer();
				
				if (SymbolicInstructionFactory.regressMode) {
					String output = "##STRING PC: (UNSAT) " + pc;
					System.out.println(output);
				}
				
				return false;
			}
			/* check if there was a timeout */
			checkTimeOut();
			//println ("[isSatisfiable] Solution: " + global_graph.toString());
			
			//Get the solutions from graph and place back into symbolic strings
			Vertex temp;
			for (Edge e: global_graph.getEdges()) {
				if (!(e instanceof EdgeConcat)) {
					//println ("[isSatisfiable] edge: " + e.getSource().uniqueName() + " - "+ e.getDest().uniqueName());
					List<StringSymbolic> represents = e.getSource().getRepresents();
					if (represents != null) {
						for (StringSymbolic ss: represents) {
							temp = global_graph.findVertex(e.getSource().getName());
							//println ("[isSatisfiable] Setting " + ss.getName() + " to '" + temp.getSolution() + "'");
							ss.solution = temp.getSolution();
							if (!setOfSolution.contains(ss)) setOfSolution.add(ss);
						}
					}
					represents = e.getDest().getRepresents();
					if (represents != null) {
						for (StringSymbolic ss: represents) {
							temp = global_graph.findVertex(e.getDest().getName());
							//println ("[isSatisfiable] Setting " + ss.getName() + " to '" + temp.getSolution() + "'");						
							ss.solution = temp.getSolution();
							if (!setOfSolution.contains(ss)) setOfSolution.add(ss);
						}
					}
				}
				else {
					List<StringSymbolic> represents = e.getSources().get(0).getRepresents();
					if (represents != null) {
						for (StringSymbolic ss: represents) {
							temp = global_graph.findVertex(e.getSources().get(0).getName());
							//println ("[isSatisfiable] 1. Setting " + ss.getName() + " to '" + temp.getSolution() + "'");
							ss.solution = temp.getSolution();
							if (!setOfSolution.contains(ss)) setOfSolution.add(ss);
						}
					}
					represents = e.getSources().get(1).getRepresents();
					if (represents != null) {
						for (StringSymbolic ss: represents) {
							temp = global_graph.findVertex(e.getSources().get(1).getName());
							//println ("[isSatisfiable] 2. Setting " + ss.getName() + " to '" + temp.getSolution() + "'");
							ss.solution = temp.getSolution();
							if (!setOfSolution.contains(ss)) setOfSolution.add(ss);
						}
					}
					represents = e.getDest().getRepresents();
					if (represents != null) {
						for (StringSymbolic ss: represents) {
							temp = global_graph.findVertex(e.getDest().getName());
							//println ("[isSatisfiable] 3. Setting " + ss.getName() + " to '" + temp.getSolution() + "'");
							ss.solution = temp.getSolution();
							if (!setOfSolution.contains(ss)) setOfSolution.add(ss);
						}
					}
				}
			}
			//println ("Translating back");
			//if (global_graph.getEdges().size() == 0) {
			for (Vertex v: global_graph.getVertices()) {
				boolean inEdge = false;
				for (Edge e: global_graph.getEdges()) {
					if (e.isHyper() && (e.getSources().get(0).equals (v) || e.getSources().get(1).equals (v) || e.getDest().equals(v))) {
						inEdge = true;
					}
					else if (!e.isHyper() && (e.getSource().equals (v) || e.getDest().equals(v))) {
						inEdge = true;
					}
				}
				if (inEdge) {
					continue;
				}
				List<StringSymbolic> represents = v.getRepresents();
				for (StringSymbolic ss: represents) {
					//println ("[isSatisfiable] Setting " + ss.getName() + " to '" + v.getSolution() + "'");
					ss.solution = v.getSolution();
					if (!setOfSolution.contains(ss)) setOfSolution.add(ss);
				}
			}
			//println ("Enforce that solutions are their given lengths");
			//Enforce that solutions are their given lengths
			for (Vertex v: global_graph.getVertices()) {
				while (v.getSolution().length() != v.getLength()) {
					//println (String.format("%d > %d", v.getSolution().length(), v.getLength()));
					v.setSolution(v.getSolution() + " ");
				}
				
				List<StringSymbolic> represents = v.getRepresents();
				if (represents == null) continue; 
				for (StringSymbolic ss: represents) {
					ss.solution = v.getSolution();
				}
			}
			//}
			StringPathCondition.flagSolved = true;
			//println ("StringPC: " + getSolution());
			cancelTimer();
			if (SymbolicInstructionFactory.regressMode) {
				String output = "##STRING PC: (SOLVED) " + pc;
				System.out.println(output);
			}
			return true;
		} catch (SymbolicStringTimedOutException e) {
			System.err.println("Symbolic String Executioner timed out");
			timedOut = false;
			
			if (SymbolicInstructionFactory.regressMode) {
				String output = "##STRING PC: (TIMEOUT) " + pc;
				System.out.println(output);
			}
			
			return false; // or return true?
		}
	}
	
	public static String getSolution () {
		StringBuilder sb = new StringBuilder();
		if (setOfSolution != null) {
			for (StringSymbolic ss: setOfSolution) {
				sb.append(ss.getName());
				sb.append ('[');
				sb.append(ss.solution());
				sb.append("]\n");
			}
		}
		return sb.toString();
	}
	
	/*
	 * Converts an integer-string constriant to a subgraph, which in turn
	 * is added to global_graph
	 */
	private void processIntegerConstraint (Expression e, Comparator comp, Expression other, Constraint origConstraint) {
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
			if (comp != null && comp == Comparator.NE && other instanceof IntegerConstant) {
				//println ("other: " + other);
				Vertex v1 = new Vertex ("CharAt_" + scai.index.solution() + "_" + scai.solution(), String.valueOf((char) scai.solution()), true);
				Vertex v2 = global_graph.findVertex(scai.se.getName());
				global_graph.addEdge(v2, v1, new EdgeNotCharAt("NotCharAt_" + scai.index.solution() + "_" + scai.solution(), v2, v1, scai.index, scai));
				//Necassery hack
				//TODO MAB: what is the function of this hack? it makes the preprocessor return UNSAT on some valid constraints!
				origConstraint.setComparator(Comparator.EQ);
				global_spc.getNpc().flagSolved = false;
			}
			else {
				Vertex v1 = new Vertex ("CharAt_" + scai.index.solution() + "_" + scai.solution(), String.valueOf((char) scai.solution()), true);
				Vertex v2 = global_graph.findVertex(scai.se.getName());
				global_graph.addEdge(v2, v1, new EdgeCharAt("CharAt_" + scai.index.solution() + "_" + scai.solution(), v2, v1, scai.index, scai));
			}
			
			
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
			processIntegerConstraint(sioi.getMinIndex(), null, null, null);
			PathCondition.flagSolved = true; //TODO: Review
			
		}
		else if (e instanceof SymbolicLastIndexOfChar2Integer) {
			SymbolicLastIndexOfChar2Integer sioi = (SymbolicLastIndexOfChar2Integer) e;
			//println ("[processIntegerConstraint] Found indexOf (char) constraint with " + sioi.getName());
			StringGraph source = convertToGraph (sioi.source);
			Vertex v1 = new Vertex ("CHAR_" + sioi.getExpression().solution(), 1);
			global_graph.addVertex(v1);
			global_graph.mergeIn(source);
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeLastIndexOfChar2("EdgeIndexOfChar_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			processIntegerConstraint(sioi.getMinDist(), null, null, null);
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
				v1 = new Vertex ("CHAR_" + sioi.getName(), 1);
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
				v1 = new Vertex ("CHAR_" + sioi.getName(), 1);
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
			Vertex v1 = new Vertex ("CHAR_" + sioi.getName(), 1);
			global_graph.addVertex(v1);
			global_graph.mergeIn(source);
			Vertex v2 = global_graph.findVertex(sioi.source.getName());
			global_graph.addEdge(v2, v1, new EdgeIndexOfChar2("EdgeIndexOfChar_" + v2.getName () + "_" + v1.getName(), v2, v1, sioi));
			processIntegerConstraint(sioi.getMinDist(), null, null, null);
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
			processIntegerConstraint(sioi.getMinIndex(), null, null, null);
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
		
		//println("\nSCL: " + sc.left);
		//println("\nSCR: " + sc.right);
		//println("\nSCC: " + sc.comp);

		
		
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
			if (v1 == null) {
				System.out.println("Could not find v1: " + se_left.getName());
			}
			if (v2 == null) {
				System.out.println("Could not find v2: " + se_right.getName());
			}
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
			//println("LEFT GRAPH: \n" + leftGraph.toDot());
			rightGraph = convertToGraph (se_right);			
			//println("RIGHT GRAPH: \n" + rightGraph.toDot());
			
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
	
	public static void checkTimeOut () {
		//println ("[checkTimeOut] checking timed out");
		synchronized (mutexTimedOut) {
			if (timedOut) {
				throw new SymbolicStringTimedOutException();
			}
		}
	}
	
	public static void cancelTimer () {
		if (TIMEOUT > 0) {
			timer.cancel();
			synchronized (mutexTimedOut) {
				timedOut = false;
			}
		}
	}

	public void solve(StringPathCondition stringPathCondition) {
		// TODO Auto-generated method stub
		
	}
	
}

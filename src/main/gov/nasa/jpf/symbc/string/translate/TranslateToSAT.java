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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import aima.core.logic.propositional.parsing.ast.BinarySentence;
import aima.core.logic.propositional.parsing.ast.Sentence;
import aima.core.logic.propositional.parsing.ast.Symbol;
import aima.core.logic.propositional.parsing.ast.UnarySentence;
import aima.core.logic.propositional.visitors.CNFClauseGatherer;
import aima.core.logic.propositional.visitors.CNFTransformer;

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

public class TranslateToSAT {
	
	private static ISolver solver;
	/* This number can be calculated beforehand */
	private static final int MAXVAR = 100000;
	
	private static Map<Vertex, Integer> map;
	private static int vectorOffset;
	
	private static boolean printClauses = false;
	private static boolean logging = true;
	
	private static SymbolicConstraintsGeneral scg;
	
	public static boolean isSat (StringGraph g, PathCondition pc) {
		if (scg == null)
			scg = new SymbolicConstraintsGeneral();
		//println ("[isSat] PC passed on: " + pc.header);
		solver = SolverFactory.newDefault();
		solver.newVar(MAXVAR);
		
		//solver.setDBSimplificationAllowed(true);
		map = new HashMap<Vertex, Integer>();
		vectorOffset = 1;
		
		//println ("[isSat] Details: ");
		for (Vertex v: g.getVertices()) {
			if (v.getSymbolicLength() instanceof SymbolicInteger) {
				SymbolicInteger si = (SymbolicInteger) v.getSymbolicLength();
				//println ("[isSat] " + si.getName() + " = " + v.getLength());
			}
			else {
				//println ("[isSat] Constant: " + v.getName() + " = " + v.getLength());
			}
		}
		
		boolean contradiction = false;
		try {
			
			for (Edge e: g.getEdges()) {
				if (e instanceof EdgeEqual) {
					if (e.getSource().getLength() != e.getDest().getLength()) {
						//println ("[isSat] " + e.getSource().getName() + " can not be equal to " + e.getDest().getName());
						return false;
					}
					handleEdgeEqual (e);
				}
				else if (e instanceof EdgeNotEqual) {
					if (e.getSource().getLength() != e.getDest().getLength()) {
						continue;
					}
					handleEdgeNotEqual (e);
				}
				else if (e instanceof EdgeStartsWith) {
					handleEdgeStartsWith (e);
				}
				else if (e instanceof EdgeNotStartsWith) {
					handleEdgeNotStartsWith(e);
				}
				else if (e instanceof EdgeTrimEqual) {
					if (e.getSource().getLength() < e.getDest().getLength()) {
						//println ("[isSat] EdgeTrimeEqual is impossible due to source's length being less then destination's length");
						return false;
					}
					handleEdgeTrimEqual(e);
				}
				else if (e instanceof EdgeSubstring1Equal) {
					if (e.getSource().getLength() < e.getDest().getLength()) {
						//println ("[isSat] EdgeSubstring1Equal is impossible due to source's length being less then destination's length");
						return false;						
					}
					handleEdgeSubstring1Equal ((EdgeSubstring1Equal) e);
				}
				else if (e instanceof EdgeSubstring2Equal) {
					if (e.getSource().getLength() < e.getDest().getLength()) {
						//println ("[isSat] EdgeSubstring2Equal is impossible due to source's length being less then destination's length");
						return false;						
					}
					handleEdgeSubstring2Equal ((EdgeSubstring2Equal) e);
				}
				else if (e instanceof EdgeEndsWith) {
					handleEdgeEndsWith (e);
				}
				else if (e instanceof EdgeNotEndsWith) {
					handleEdgeNotEndsWith(e);
				}
				else if (e instanceof EdgeConcat) {
					handleEdgeConcat ((EdgeConcat) e);
				}
				else if (e instanceof EdgeCharAt) {
					boolean result = handleEdgeCharAt ((EdgeCharAt) e);
					if (!result) {
						//println ("[isSat] Unsat, current charAt not valid");
						return false;
					}
				}
				else if (e instanceof EdgeIndexOf) {
					handleEdgeIndexof ((EdgeIndexOf) e);
				}
				else if (e instanceof EdgeContains) {
					handleEdgeContains (e);
				}
				else if (e instanceof EdgeNotContains) {
					handleEdgeNotContains (e);
				}
				else {
					//Not handled yet
					//println ("Not handled yet: " + e.getClass());
					return true;
				}
			}
		} catch (ContradictionException e) {
			//e.printStackTrace();
			//println ("[isSat] Contradiction!");
			//System.exit(0);
			contradiction = true;
		}
		IProblem problem = solver;
		int roundrobinLengthen = 0;
		boolean nonEqualitySatisfied = false;
		boolean sat = false;
		try {
			while (!contradiction && solver.isSatisfiable() && !nonEqualitySatisfied) {
				nonEqualitySatisfied = true;
				//println ("Sat!");
				sat = true;
				int[] solution = problem.model();
				//printClause (solution); 
				for (Entry<Vertex, Integer> e: map.entrySet()) {
					if (e.getKey().isConstant()) {
						//println ("[isSat] Solution at this moment: " + e.getKey().getSolution());
					}
					int offset = e.getValue() - 1;
					int length = e.getKey().getLength();
					for (int i = 0; i < length; i++) {
						for (int k = 0; k < SymbolicStringConstraintsGeneral.DIFF_CHAR; k++) {
							if (solution[offset + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + k] > 0) {
								e.getKey().setCharSolution((char) (SymbolicStringConstraintsGeneral.MIN_CHAR + k), i);
							}
						}
					}
					if (e.getKey().getSolution().length() == 0) {
						e.getKey().setSolution(" ");
					}
					else {
						//println ("[isSat] length = " + e.getKey().getSolution().length());
					}
					//println ("[isSat] " + e.getKey().getName() + " solution is '" + e.getKey().getSolution() + "'");
				}
				/* Lazy inequality */
				for (Edge e: g.getEdges()) {
					if (e instanceof EdgeNotEqual) {
						//Should maybe remember this
						if (e.getSource().getSolution().equals (e.getDest().getSolution())) {
							nonEqualitySatisfied = false;
							for (int i = 0; i < solution.length; i++) {
								solution[i] = solution[i] * -1;
							}
							//println ("[isSat] Adding back inequality, becuase '" +e.getSource().getSolution() + "' (" +e.getSource().getName() +") == '" + e.getDest().getSolution() + "' ("+e.getDest().getName()+")");
							//printClause (solution);
							solver.addClause(new VecInt(solution));
							sat = false;
							break; /* First resolve this issue before going on */
						}
					}
					else if (e instanceof EdgeNotStartsWith) {
						if (e.getSource().getSolution().startsWith(e.getDest().getSolution())) {
							nonEqualitySatisfied = false;
							for (int i = 0; i < solution.length; i++) {
								solution[i] = solution[i] * -1;
							}
							//println ("[isSat] Adding back inequality, becuase '" +e.getSource().getSolution() + "' (" +e.getSource().getName() +") startswith '" + e.getDest().getSolution() + "' ("+e.getDest().getName()+")");
							//printClause (solution);
							solver.addClause(new VecInt(solution));
							sat = false;
							break; /* First resolve this issue before going on */
						}
					}
					else if (e instanceof EdgeNotEndsWith) {
						if (e.getSource().getSolution().endsWith(e.getDest().getSolution())) {
							nonEqualitySatisfied = false;
							for (int i = 0; i < solution.length; i++) {
								solution[i] = solution[i] * -1;
							}
							//println ("[isSat] Adding back inequality, becuase '" +e.getSource().getSolution() + "' (" +e.getSource().getName() +") endswith '" + e.getDest().getSolution() + "' ("+e.getDest().getName()+")");
							//printClause (solution);
							solver.addClause(new VecInt(solution));
							sat = false;
							break; /* First resolve this issue before going on */
						}
					}
					else if (e instanceof EdgeIndexOf) {
						EdgeIndexOf eio = (EdgeIndexOf) e;
						int indexOfValue = e.getSource().getSolution().indexOf(e.getDest().getSolution());
						if (indexOfValue != eio.getIndex().solution()) {
							nonEqualitySatisfied = false;
							for (int i = 0; i < solution.length; i++) {
								solution[i] = solution[i] * -1;
							}
							//println ("[isSat] Adding back inequality, becuase '" +e.getSource().getSolution() + "' (" +e.getSource().getName() +") indexOf '" + e.getDest().getSolution() + "' ("+e.getDest().getName()+") != " + eio.getIndex().solution());
							//printClause (solution);
							solver.addClause(new VecInt(solution));
							sat = false;
							if (indexOfValue > -1) {
								//It has already been found earlier, thus the eio.getIndex(), must be equaled to it or less
								pc._addDet(Comparator.LE, eio.getIndex(), indexOfValue);
								if (scg.isSatisfiable(pc)) {
									scg.solve(pc);
									PathCondition.flagSolved = true; 
								}
								else {
									//println ("[isSat] indexOf could not be satisfied");
									return false;
								}
							}
							break; /* First resolve this issue before going on */
						}
					}
					else if (e instanceof EdgeNotContains) {
						if (e.getSource().getSolution().contains(e.getDest().getSolution())) {
							nonEqualitySatisfied = false;
							for (int i = 0; i < solution.length; i++) {
								solution[i] = solution[i] * -1;
							}
							//println ("[isSat] Adding back inequality, becuase '" +e.getSource().getSolution() + "' (" +e.getSource().getName() +") contains '" + e.getDest().getSolution() + "' ("+e.getDest().getName()+")");
							//printClause (solution);
							solver.addClause(new VecInt(solution));
							sat = false;
							break; /* First resolve this issue before going on */
						}
					}
					else if (e instanceof EdgeContains) {
						if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
							if (!e.getSource().getSolution().contains(e.getDest().getSolution())) {
								nonEqualitySatisfied = false;
								for (int i = 0; i < solution.length; i++) {
									solution[i] = solution[i] * -1;
								}
								//println ("[isSat] Adding back inequality, becuase '" +e.getSource().getSolution() + "' (" +e.getSource().getName() +") does not contain '" + e.getDest().getSolution() + "' ("+e.getDest().getName()+")");
								//printClause (solution);
								solver.addClause(new VecInt(solution));
								sat = false;
								break; /* First resolve this issue before going on */
							}
						}
					}
				}
				
			}
		} catch (TimeoutException e) {
			e.printStackTrace();
		} catch (ContradictionException e) {
			//println ("[isSat]Assuming unsat!");
			sat = false;
		}
			
		//try {	
			if (!sat) {
				//println ("Unsat!, attempting to lengthen vertices");
				//SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
				//This forces that the graph should not change during the SAT solving
				//First check if any change to the values of the charAt's in the graph will make a difference
				/*for (Edge e: g.getEdges()) {
					if (e instanceof EdgeCharAt) {
						EdgeCharAt eca = (EdgeCharAt) e;
						pc._addDet(Comparator.LE, new IntegerConstant(SymbolicStringConstraintsSAT.MIN_CHAR), eca.getValue());
						pc._addDet(Comparator.LT, eca.getValue(), new IntegerConstant(SymbolicStringConstraintsSAT.MAX_CHAR));
					}
				}

				if (!scg.isSatisfiable(pc)) {
					scg.solve(pc);
					PathCondition.flagSolved = true;
					System.out.//println("[isSat] PC: " + pc.header);
					//println ("[isSat] Current charAt index's won't work");
					LinearOrIntegerConstraints loic = new LinearOrIntegerConstraints();
					for (Edge e: g.getEdges()) {
						if (e instanceof EdgeCharAt) {
							EdgeCharAt eca = (EdgeCharAt) e;
							loic.addToList(new LinearIntegerConstraint(eca.getIndex(), Comparator.NE, new IntegerConstant(eca.getIndex().solution())));
						}
					}
					pc._addDet(loic);
				}*/
			
				//Continue finding the solution...
				scg.solve(pc);
				PathCondition.flagSolved = true;
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				for (Entry<Vertex, Integer> e: map.entrySet()) {
					loic.addToList(new LinearIntegerConstraint(e.getKey().getSymbolicLength(), Comparator.NE, new IntegerConstant (e.getKey().getLength())));
				}
				for (Edge e: g.getEdges()) {
					if (e instanceof EdgeCharAt) {
						EdgeCharAt eca = (EdgeCharAt) e;
						loic.addToList(new LinearIntegerConstraint(eca.getIndex(), Comparator.NE, new IntegerConstant(eca.getIndex().solution())));
						loic.addToList(new LinearIntegerConstraint(eca.getValue(), Comparator.NE, new IntegerConstant(eca.getValue().solution())));
					}
					else if (e instanceof EdgeIndexOf) {
						EdgeIndexOf eio = (EdgeIndexOf) e;
						loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution)));
					}
				}
				//println ("[isSat] Ors: " + loic);
				pc._addDet(loic);
				//println ("[isSat] PC: " + pc.header);
				
				if (scg.isSatisfiable(pc)) {
					scg.solve(pc);
					pc.flagSolved = true;
					//println ("[isSat] solved PC: " + pc.header);
					return isSat (g, pc); //TODO: Prevent infinite looping
				}
				else {
					//println ("[isSat] With the added constraint, could not be solved");
					return false;
				}
			}
			
		/*} catch (TimeoutException e) {
			e.printStackTrace();
			return true;
		} catch (ContradictionException e) {
			System.err.//println(g.toDot());
			e.printStackTrace();
			System.exit(0);
			return true;
		}*/
		return true;
	}
	
	private static boolean handleEdgeCharAt (EdgeCharAt e) throws ContradictionException{
		//Constant cases should be handeld by the preprocessor
		if (!e.getSource().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			int index = e.getIndex().solutionInt();
			int character = e.getValue().solutionInt() - SymbolicStringConstraintsGeneral.MIN_CHAR;
			int clause[] = new int [1];
			clause[0] = vector1 + index * SymbolicStringConstraintsGeneral.DIFF_CHAR + character;
			//printClause(clause);
			solver.addClause(new VecInt(clause));
			return true;
		}
		else {
			//throw new RuntimeException ("Unexpected");
			String constantString = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			//int character = e.getValue().solution() - SymbolicStringConstraintsSAT.MIN_CHAR;
			if (constantString.charAt(index) != (char) e.getValue().solution()) {
				return false;
			}
			return true;
		}
	}
	
	private static int retrieveInt (Vertex v) throws ContradictionException{
		Integer i = map.get(v);
		
		if (i == null) {
			//println (v.getName() + " start ...");
			map.put (v, new Integer(vectorOffset));
			//Apply the basic rules to the Vertex
			int[] clause = new int [SymbolicStringConstraintsGeneral.DIFF_CHAR];
			
			for (int k = 0; k < v.getLength(); k++) { 
				for (int j = 0; j < SymbolicStringConstraintsGeneral.DIFF_CHAR; j++) {
					clause[j] = vectorOffset + k * SymbolicStringConstraintsGeneral.DIFF_CHAR + j; 
				}
				//printClause(clause);
				//solver.addClause(new VecInt(clause));
				solver.addAtLeast(new VecInt(clause), 1);
				solver.addAtMost(new VecInt(clause), 1);
				
			}
			
			/*for (int k = 0; k < v.getLength(); k++) { 
				for (int j = 0; j < DIFF_CHAR; j++) {
					clause[j] = (vectorOffset + k * v.getLength() + j) * -1; 
				}
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
			
			for (int k = 0; k < v.getLength(); k++) { 
				for (int j = 0; j < DIFF_CHAR; j++) {
					clause[j] = (vectorOffset + k * v.getLength() + j) * -1; 
				}
				for (int l = 0; l < DIFF_CHAR; l++) {
					if (l > 0) clause[l-1] = clause[l-1] * -1;
					clause [l] = clause[l] * -1;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
				}
			}*/
			//println (v.getName() + " end");
			vectorOffset += v.getLength() * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			return vectorOffset - v.getLength() * SymbolicStringConstraintsGeneral.DIFF_CHAR;
		}
		
		return i;
	}
	
	private static void println (String s) {
		System.out.println("[TranslateToSAT] " + s);
	}
	
	private static void printClause (int[] c) {
		if (printClauses) {
			for (int i: c) {
				System.out.print(i + " ");
			}
			System.out.println();
		}
	}
	
	private static boolean logicalXOR(boolean x, boolean y) {
	    return ( ( x || y ) && ! ( x && y ) );
	}
	
	private static void handleEdgeNotContains (Edge e) throws ContradictionException {
		if (!e.getSource().isConstant()) {
			retrieveInt(e.getSource());
		}
		if (!e.getDest().isConstant()) {
			retrieveInt(e.getDest());
		}
		
		//Handle lazily
	}
	
	private static void handleEdgeContains (Edge e) throws ContradictionException {
		
		if (e.getSource().getLength() == e.getDest().getLength()) {
			handleEdgeEqual(e);
			return;
		}
		
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			//Can't statically enforce this, causes exponential blowup when encoding it to SAT
			retrieveInt(e.getSource());
			retrieveInt(e.getDest());
		}
		else if (!e.getSource().isConstant()){
			Vertex symbolicVertex, constantVertex;
			symbolicVertex = e.getSource();
			constantVertex = e.getDest();
			int vector1 = retrieveInt(symbolicVertex);
			
			//TODO: Add if constant's size is larger then symbolic then unsat
			
			//DNF
			String constantString = constantVertex.getSolution();
			int [][] listOfClauses = new int [symbolicVertex.getLength() - constantString.length()+1][constantVertex.getLength()];
			for (int i = 0; i < symbolicVertex.getLength() - constantString.length()+1; i++) {
				int clause[] = new int[constantVertex.getLength()];
				char c;
				int offset;
				for (int j = i; j < i + constantVertex.getLength(); j++) {
					c = constantString.charAt(j - i);
					offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
					clause[j - i] = vector1 + j * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
				}
				//printClause(clause);
				listOfClauses[i] = clause;
			}
			
			//DNF->CNF
			Sentence sentence = convert(listOfClauses);
			CNFTransformer transformer = new CNFTransformer();
			//println ("[handleEdgeContains] sentence: " + sentence);
			sentence = transformer.transform(sentence);
			//println ("[handleEdgeContains] cnf: " + sentence);
			//CNFClauseGatherer cg =new CNFClauseGatherer();
			//Has trouble with only one clause [fixed]
			//println ("[handleEdgeContains] clauses: " + CNFExtra.extractClauses(sentence));
			List<List<Symbol>> temp = CNFExtra.idempotency(CNFExtra.extractClauses(sentence));
			//println ("[handleEdgeContains] ans2: " + temp);
			temp = CNFExtra.absorb(temp);
			temp = CNFExtra.remDup(temp);
			//println ("[handleEdgeContains] ans3: " + temp);
			
			//println ("[handleEdgeContains] cons start");
			for (List<Symbol> c: temp) {
				int clause[] = new int[c.size()];
				for (int i = 0; i < c.size(); i++) {
					clause[i] = Integer.parseInt(c.get(i).getValue());
				}
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
			//println ("[handleEdgeContains] cons end");
			
		}
		else if (!e.getDest().isConstant()) {
			int vector1 = retrieveInt (e.getDest());
			String constantString = e.getSource().getSolution();
			
			//DNF
			//println ("[handleEdgeContains] DNF:");
			int[][]listOfClauses = new int[constantString.length() - e.getDest().getLength()+1][e.getDest().getLength()];
			for (int i = 0; i < constantString.length() - e.getDest().getLength()+1; i++) {
				int clause[] = new int[e.getDest().getLength()];
				
				char c;
				int offset;
				for (int j = i; j < i + e.getDest().getLength(); j++) {
					c = constantString.charAt(j - i);
					offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
					clause[j - i] = vector1 + j * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
				}
				listOfClauses[i] = clause;
				//printClause (clause);
			}
			//println ("[handleEdgeContains] end");
			
			//DNF->CNF
			Sentence sentence = convert(listOfClauses);
			CNFTransformer transformer = new CNFTransformer();
			//println ("[handleEdgeContains] sentence: " + sentence);
			sentence = transformer.transform(sentence);
			//println ("[handleEdgeContains] cnf: " + sentence);
			//CNFClauseGatherer cg =new CNFClauseGatherer();
			//Has trouble with only one clause [fixed]
			//println ("[handleEdgeContains] clauses: " + CNFExtra.extractClauses(sentence));
			List<List<Symbol>> temp = CNFExtra.idempotency(CNFExtra.extractClauses(sentence));
			//println ("[handleEdgeContains] ans2: " + temp);
			temp = CNFExtra.absorb(temp);
			temp = CNFExtra.remDup(temp);
			//println ("[handleEdgeContains] ans3: " + temp);
			
			//println ("[handleEdgeContains] cons start");
			for (List<Symbol> c: temp) {
				int clause[] = new int[c.size()];
				for (int i = 0; i < c.size(); i++) {
					clause[i] = Integer.parseInt(c.get(i).getValue());
				}
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
			//println ("[handleEdgeContains] cons end");
			
		}
	}
	
	private static void handleEdgeConcat (Edge e) throws ContradictionException {
		if (e.getSources().get(0).getLength() + e.getSources().get(1).getLength() != e.getDest().getLength()) {
			throw new RuntimeException("Preprocessor fudged up");
		}
		//println ("Concat start...");
		if (e.getDest().isConstant()) {
			if (!e.getSources().get(0).isConstant() && !e.getSources().get(1).isConstant()) {
				int vector1 = retrieveInt(e.getSources().get(0));
				int vector2 = retrieveInt(e.getSources().get(1));
				
				int lengthOfLeft = e.getSources().get(0).getLength();
				int lengthOfRight = e.getSources().get(1).getLength();
				
				int clause[] = new int [1];
				
				for (int i = 0; i < lengthOfLeft; i++) {
					char character = e.getDest().getSolution().charAt(i);
					int offset = character - SymbolicStringConstraintsGeneral.MIN_CHAR;
					clause[0] = vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
				}
				for (int i = 0; i < lengthOfRight; i++) {
					char character = e.getDest().getSolution().charAt(i + lengthOfLeft);
					int offset = character - SymbolicStringConstraintsGeneral.MIN_CHAR;
					clause[0] = vector2 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
				}
				
			}
			else if (logicalXOR(e.getSources().get(0).isConstant(), e.getSources().get(1).isConstant())) {
				Vertex constantVertex;
				
				if (e.getSources().get(0).isConstant()) {
					int vector1 = retrieveInt(e.getSources().get(1));
					constantVertex = e.getSources().get(0);
					String leftPart = constantVertex.getSolution();
					String constantPart = StringUtility.findRightSide (e.getDest().getSolution(), leftPart);
					int clause[] = new int [1];
					for (int i = 0; i < constantPart.length(); i++) {
						char character = constantPart.charAt(i);
						int offset = character - SymbolicStringConstraintsGeneral.MIN_CHAR;
						clause[0] = vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
						//printClause(clause);
						solver.addClause(new VecInt(clause));
					}
				}
				else {
					//Right one is constant
					int vector1 = retrieveInt(e.getSources().get(0));
					constantVertex = e.getSources().get(1);
					String rightPart = constantVertex.getSolution();
					String constantPart = StringUtility.findLeftSide (e.getDest().getSolution(), rightPart);
					////println ("[handleEdgeConcat] Constant Part = " + constantPart);
					int clause[] = new int [1];
					for (int i = 0; i < constantPart.length(); i++) {
						char character = constantPart.charAt(i);
						int offset = character - SymbolicStringConstraintsGeneral.MIN_CHAR;
						clause[0] = vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
						//printClause(clause);
						solver.addClause(new VecInt(clause));
					}
				}
				
			}
			else {
				//Both are constant, prepocessor should handle this.
				//throw new RuntimeException ("Preprocessor fudged up");
			}
		}
		else if (!e.getDest().isConstant()) {
			if (!e.getSources().get(0).isConstant() && !e.getSources().get(1).isConstant()) {
				int vector1 = retrieveInt(e.getSources().get(0));
				int vector2 = retrieveInt(e.getSources().get(1));
				int vector3 = retrieveInt(e.getDest());
				
				int lengthOfLeft = e.getSources().get(0).getLength();
				int lengthOfRight = e.getSources().get(1).getLength();
				int lengthOfDest = e.getDest().getLength();
				
				int vectorLengthOfLeft = lengthOfLeft * SymbolicStringConstraintsGeneral.DIFF_CHAR;
				int vectorLengthOfRight = lengthOfRight * SymbolicStringConstraintsGeneral.DIFF_CHAR;
				int vectorLengthOfDest = lengthOfDest * SymbolicStringConstraintsGeneral.DIFF_CHAR;
				int clause[] = new int [2];
				//println ("Concat start...");
				for (int i = 0; i < vectorLengthOfLeft; i++) {
					clause[0] = (vector1 + i) * -1;
					clause[1] = vector3 + i;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
					clause[0] = vector1 + i;
					clause[1] = (vector3 + i) * -1;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
				}
				for (int i = 0; i < vectorLengthOfRight; i++) {
					clause[0] = (vector2 + i) * -1;
					clause[1] = vector3 + vectorLengthOfLeft + i;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
					clause[0] = vector2 + i;
					clause[1] = (vector3 + vectorLengthOfLeft + i) * -1;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
				}
				//println ("Concat end");
			}
			else if (logicalXOR(e.getSources().get(0).isConstant(), e.getSources().get(1).isConstant())) {
				Vertex constantVertex;
				
				if (e.getSources().get(0).isConstant()) {
					int vector2 = retrieveInt(e.getSources().get(1));
					int vector3 = retrieveInt(e.getDest());
					
					int lengthOfLeft = e.getSources().get(0).getLength();
					int lengthOfRight = e.getSources().get(1).getLength();
					int lengthOfDest = e.getDest().getLength();
					
					int vectorLengthOfLeft = lengthOfLeft * SymbolicStringConstraintsGeneral.DIFF_CHAR;
					int vectorLengthOfRight = lengthOfRight * SymbolicStringConstraintsGeneral.DIFF_CHAR;
					int vectorLengthOfDest = lengthOfDest * SymbolicStringConstraintsGeneral.DIFF_CHAR;
					
					String constantString = e.getSources().get(0).getSolution(); 
					
					int clause[] = new int [1];
					for (int i = 0; i < lengthOfLeft; i++) {
						char character = constantString.charAt(i);
						int offset = character - SymbolicStringConstraintsGeneral.MIN_CHAR;
						clause[0] = vector3 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
						//printClause(clause);
						solver.addClause(new VecInt(clause));
					}
					clause = new int[2];
					for (int i = 0; i < vectorLengthOfRight; i++) {
						clause[0] = (vector2 + i) * -1;
						clause[1] = vector3 + vectorLengthOfLeft + i;
						//printClause(clause);
						solver.addClause(new VecInt(clause));
						clause[0] = vector2 + i;
						clause[1] = (vector3 + vectorLengthOfLeft + i) * -1;
						//printClause(clause);
						solver.addClause(new VecInt(clause));
					}
				}
				else {
					//Right one is constant
					int vector1 = retrieveInt(e.getSources().get(0));
					int vector3 = retrieveInt(e.getDest());
					
					int lengthOfLeft = e.getSources().get(0).getLength();
					int lengthOfRight = e.getSources().get(1).getLength();
					int lengthOfDest = e.getDest().getLength();
					
					int vectorLengthOfLeft = lengthOfLeft * SymbolicStringConstraintsGeneral.DIFF_CHAR;
					int vectorLengthOfRight = lengthOfRight * SymbolicStringConstraintsGeneral.DIFF_CHAR;
					int vectorLengthOfDest = lengthOfDest * SymbolicStringConstraintsGeneral.DIFF_CHAR;
					
					String constantString = e.getSources().get(1).getSolution();
					
					int clause[] = new int [2];
					for (int i = 0; i < vectorLengthOfLeft; i++) {
						clause[0] = (vector1 + i) * -1;
						clause[1] = vector3 + i;
						//printClause(clause);
						solver.addClause(new VecInt(clause));
						clause[0] = vector1 + i;
						clause[1] = (vector3 + i) * -1;
						//printClause(clause);
						solver.addClause(new VecInt(clause));
					}
					clause = new int [1];
					for (int i = 0; i < lengthOfRight; i++) {
						char character = constantString.charAt(i);
						int offset = character - SymbolicStringConstraintsGeneral.MIN_CHAR;
						clause[0] = vector3 + (i + lengthOfLeft)* SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
						//printClause(clause);
						solver.addClause(new VecInt(clause));
					}
					
				}
				
			}
			else {
				//All three are constant, prepocessor should handle this.
				//throw new RuntimeException ("Preprocessor fudged up");
			}
		}
		//println ("Concat end");
	}
	
	
	
	private static void handleEdgeEqual (Edge e) throws ContradictionException{
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			int vector2 = retrieveInt(e.getDest());
			
			int length = e.getSource().getLength();
			
			int vectorLength = length * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			int clause[] = new int[2];
			//println ("Equal start...");
			for (int i = 0; i < vectorLength; i++) {
				clause[0] = (vector1 + i) * -1;
				clause[1] = vector2 + i;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
				clause[0] = vector1 + i;
				clause[1] = (vector2 + i) * -1;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
			//println ("Equal end");
		}
		else if (e.getSource().isConstant()) {
			int vector2 = retrieveInt(e.getDest());
			
			int length = e.getSource().getLength();
			
			if (e.getSource().getLength() != e.getDest().getLength()) {
				throw new RuntimeException("Preprocesser failed");
			}
			
			int clause[] = new int[1];
			char c;
			int offset;
			for (int i = 0; i < length; i++) {
				c = e.getSource().getSolution().charAt(i);
				offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
				clause[0] = vector2 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
		}
		else if (e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			
			int length = e.getSource().getLength();
			
			if (e.getSource().getLength() != e.getDest().getLength()) {
				throw new RuntimeException("Preprocesser failed");
			}
			
			int clause[] = new int[1];
			char c;
			int offset;
			for (int i = 0; i < length; i++) {
				c = e.getDest().getSolution().charAt(i);
				offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
				clause[0] = vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
		}
		else {
			//println ("[handleEdgeEqual] Something is wrong here");
		}
	}
	
	private static void handleEdgeSubstring1Equal (EdgeSubstring1Equal e) throws ContradictionException{
		
		if (e.getSource().getLength() == e.getDest().getLength()) {
			//println ("[handleEdgeSubstring1Equal] Handing over to normal equals");
			handleEdgeEqual(e);
		}
		
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			int vector2 = retrieveInt(e.getDest());
			
			int lengthOfSource = e.getSource().getLength();
			int lengthOfDest = e.getDest().getLength();
			
			int vectorLengthOfSource = lengthOfSource * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			int vectorLengthOfDest = lengthOfDest * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			
			int offsetInSource = e.getArgument1() * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			
			int clause[] = new int[2];
			//println ("Substring start...");
			for (int i = 0; i < vectorLengthOfDest; i++) {
				clause[0] = (vector1 + offsetInSource + i) * -1;
				clause[1] = vector2 + i;
				
				//printClause(clause);
				solver.addClause(new VecInt(clause));
				clause[0] = vector1 + offsetInSource + i;
				clause[1] = (vector2 + i) * -1;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
			//println ("Substring end");
		}
		else if (e.getSource().isConstant()) {
			throw new RuntimeException ("Symbolic Integers not supported yet");
/*			int vector2 = retrieveInt(e.getDest());
			
			int length = e.getSource().getLength();
			
			int clause[] = new int[1];
			char c;
			int offset;
			for (int i = e.getArgument1(); i < length; i++) {
				c = e.getSource().getSolution().charAt(i);
				offset = c - SymbolicStringConstraintsSAT.MIN_CHAR;
				clause[0] = vector2 + i * SymbolicStringConstraintsSAT.DIFF_CHAR + offset;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}*/
		}
		else if (e.getDest().isConstant()) {
			//throw new RuntimeException("Oversite");
			int vector1 = retrieveInt(e.getSource());
			int length = e.getDest().getLength();
			
			int clause[] = new int [1];
			char c;
			int offset;
			for (int i = e.getArgument1(); i < e.getArgument1() + length; i++) {
				c = e.getDest().getSolution().charAt(i - e.getArgument1());
				offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
				clause[0] = vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
				//printClause (clause);
				solver.addClause(new VecInt(clause));
			}
		}
		else {
			//println ("[handleEdgeSubstring1Equal] Something is wrong here");
		}
		
	}
	
	private static void handleEdgeSubstring2Equal (EdgeSubstring2Equal e) throws ContradictionException{
		
		if (e.getSource().getLength() == e.getDest().getLength()) {
			//println ("[handleEdgeSubstring1Equal] Handing over to normal equals");
			handleEdgeEqual(e);
		}
		
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			int vector2 = retrieveInt(e.getDest());
			
			int lengthOfSource = e.getSource().getLength();
			int lengthOfDest = e.getDest().getLength();
			
			int vectorLengthOfSource = lengthOfSource * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			int vectorLengthOfDest = lengthOfDest * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			
			int offsetInSource = e.getArgument1() * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			//int endOffsetInSource = e.getArgument2() * DIFF_CHAR;
			
			int clause[] = new int[2];
			//println ("Substring start...");
			for (int i = 0; i < vectorLengthOfDest; i++) {
				clause[0] = (vector1 + offsetInSource + i) * -1;
				clause[1] = vector2 + i;
				
				//printClause(clause);
				solver.addClause(new VecInt(clause));
				clause[0] = vector1 + offsetInSource + i;
				clause[1] = (vector2 + i) * -1;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
			//println ("Substring end");
		}
		else if (e.getSource().isConstant()) {
			throw new RuntimeException ("Symbolic Integers not supported yet");
/*			int vector2 = retrieveInt(e.getDest());
			
			int length = e.getSource().getLength();
			
			int clause[] = new int[1];
			char c;
			int offset;
			for (int i = e.getArgument1(); i < e.getArgument2(); i++) {
				c = e.getSource().getSolution().charAt(i);
				offset = c - SymbolicStringConstraintsSAT.MIN_CHAR;
				clause[0] = vector2 + i * SymbolicStringConstraintsSAT.DIFF_CHAR + offset;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}*/
		}
		else if (e.getDest().isConstant()) {
			//throw new RuntimeException("Oversite");
			//println ("Entered, " + e.getArgument1() + " " + e.getArgument2());
			int vector1 = retrieveInt(e.getSource());
			int length = e.getDest().getLength();
			
			int clause[] = new int [1];
			char c;
			int offset;
			for (int i = e.getArgument1(); i < e.getArgument1() + length; i++) {
				c = e.getDest().getSolution().charAt(i - e.getArgument1());
				offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
				clause[0] = vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
				//printClause (clause);
				solver.addClause(new VecInt(clause));
			}

		}
		else {
			//println ("[handleEdgeSubstring1Equal] Something is wrong here");
		}
		
	}
	
	/*
	 * Both constants should be handled by preprocessor
	 */
	private static void handleEdgeTrimEqual (Edge e) throws ContradictionException{		
		int offsetOfSpace = ((int) ' ') - SymbolicStringConstraintsGeneral.MIN_CHAR;
		if (offsetOfSpace < 0) {
			//println ("[handleEdgeTrimEqual] Can not handle space yet");
			return;
		}
		
		int lengthOfSource = e.getSource().getLength();
		int lengthOfDest = e.getDest().getLength();
		
		if (lengthOfSource == lengthOfDest) {
			//println ("[handleEdgeTrimEqual] Equal length, handing over to handleEdgeEqual");
			handleEdgeEqual(e);
			return;
		}
		
		int vectorLengthOfSource = lengthOfSource * SymbolicStringConstraintsGeneral.DIFF_CHAR;
		int vectorLengthOfDest = lengthOfDest * SymbolicStringConstraintsGeneral.DIFF_CHAR;
		
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			int vector2 = retrieveInt(e.getDest());			
			
			for (int positionOfDest = 0; positionOfDest + lengthOfDest <= lengthOfSource; positionOfDest++) {
				int clause[] = new int[lengthOfSource - lengthOfDest + 2];
				int index = 0;
				for (int i = 0; i < lengthOfSource; i++) {
					if (i >= positionOfDest && i < positionOfDest + lengthOfDest) {
						continue;
					}
					clause[index] = (vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offsetOfSpace) * -1; index++;
				}
				int oldindex = index;
				for (int j = 0; j < vectorLengthOfDest; j++) {
					index = oldindex;
					clause[index] = (vector1 + j + positionOfDest * SymbolicStringConstraintsGeneral.DIFF_CHAR) * -1; index++;
					clause[index] = vector2 + j; index = index - 1;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
					clause[index] = vector1 + j + positionOfDest * SymbolicStringConstraintsGeneral.DIFF_CHAR; index++;
					clause[index] = (vector2 + j) * -1;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
				}
			}
		}
		else if (e.getSource().isConstant()) {
			int vector2 = retrieveInt(e.getDest());
			
			String constantString = e.getSource().getSolution().trim();
			char c;
			int clause[] = new int[1];
			for (int i = 0; i < constantString.length(); i++) {
				c = constantString.charAt(i);
				int character = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
				clause[0] = vector2 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + character;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
		}
		else if (e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			
			String constantString = e.getDest().getSolution();
			int listOfClauses[][] = new int [e.getSource().getLength() - e.getDest().getLength() + 1][e.getSource().getLength()];
			int space = ' ' - SymbolicStringConstraintsGeneral.MIN_CHAR;
			//This is in DNF from
			for (int i = 0; i < e.getSource().getLength() - e.getDest().getLength() + 1; i++) {
				int clause[] = new int[e.getSource().getLength()]; //need to test lengths
				for (int j = 0; j < i; j++) {
					clause[j] = vector1 + j * SymbolicStringConstraintsGeneral.DIFF_CHAR + space;
				}
				for (int j = i; j < i + e.getDest().getLength(); j++) {
					char c = constantString.charAt(j - i);
					int offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
					clause[j] = vector1 + j * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
				}
				for (int j = i + e.getDest().getLength(); j < e.getSource().getLength(); j++) {
					clause[j] = vector1 + j * SymbolicStringConstraintsGeneral.DIFF_CHAR + space;
				}
				listOfClauses[i] = clause;
				////printClause (clause);
			}
			
			//DNF -> CNF
			Sentence sentence = convert(listOfClauses);
			CNFTransformer transformer = new CNFTransformer();
			//println ("[handleEdgeTrimEqual] sentence: " + sentence);
			sentence = transformer.transform(sentence);
			//println ("[handleEdgeTrimEqual] cnf: " + sentence);
			CNFClauseGatherer cg =new CNFClauseGatherer();
			List<List<Symbol>> temp = CNFExtra.idempotency(cg.getClausesFrom(sentence));
			//println ("[handleEdgeTrimEqual] ans2: " + temp);
			temp = CNFExtra.absorb(temp);
			temp = CNFExtra.remDup(temp);
			//println ("[handleEdgeTrimEqual] ans3: " + temp);
			
			//println ("Trim cons start");
			for (List<Symbol> c: temp) {
				int clause[] = new int[c.size()];
				for (int i = 0; i < c.size(); i++) {
					clause[i] = Integer.parseInt(c.get(i).getValue());
				}
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
			//println ("Trim cons end");
			
		}
	}
	
	private static Sentence convert (int listOfClauses[][]) {
		if (listOfClauses.length == 1) {
			return andClause(listOfClauses[0]);
		}
		else {
			BinarySentence result = new BinarySentence("OR", andClause(listOfClauses[0]), andClause(listOfClauses[1]));
			for (int i = 2; i < listOfClauses.length; i++) {
				result = new BinarySentence("OR", result, andClause(listOfClauses[i]));
			}
			return result;
		}
	}
	 
	private static Sentence convert (List<int[]> clauses) {
		if (clauses.size() == 1) {
			return andClause(clauses.get(0));
		}
		else {
			BinarySentence result = new BinarySentence("OR", andClause(clauses.get(0)), andClause(clauses.get(1)));
			for (int i = 2; i < clauses.size(); i++) {
				result = new BinarySentence("OR", result, andClause(clauses.get(i)));
			}
			return result;
		}
	}
	
	private static Sentence andClause (int clause[]) {
		if (clause.length == 1) {
			return new Symbol (String.valueOf(clause[0]));
		}
		else {
			BinarySentence result = new BinarySentence("AND", new Symbol(String.valueOf(clause[0])), new Symbol (String.valueOf(clause[1])));
			for (int i = 2; i < clause.length; i++) {
				result = new BinarySentence("AND", result, new Symbol (String.valueOf(clause[i])));
			}
			return result;
		}
	}
	
	private static Sentence andClause (Sentence c1, Sentence c2) {
		return new BinarySentence("AND", c1, c2);
	}
	
	private static Sentence orClause (Sentence c1, Sentence c2) {
		return new BinarySentence("OR", c1, c2);
	}
	
	private static Sentence createSymbol (int i) {
		if (i > 0) {
			return new Symbol (String.valueOf(i));
		}
		else if (i < 0) {
			return new UnarySentence(new Symbol(String.valueOf(i)));
		}
		else {
			return null;
		}
	}
	
	private static void handleEdgeNotEqual (Edge e) throws ContradictionException{
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			int vector2 = retrieveInt(e.getDest());
			//Handle lazily
		}
		else if (logicalXOR(e.getSource().isConstant(), e.getDest().isConstant())) {
			Vertex constantVertex, symbolicVertex;
			if (e.getSource().isConstant()) {
				constantVertex = e.getSource();
				symbolicVertex = e.getDest();
			}
			else {
				constantVertex = e.getDest();
				symbolicVertex = e.getSource();
			}
			int vector1 = retrieveInt(symbolicVertex);
			String constantString = constantVertex.getSolution();
			char c;
			int offset;
			int clause[] = new int[constantString.length()];
			for (int i = 0; i < constantString.length(); i++) {
				c = constantString.charAt(i);
				offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
				clause[i] = (vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset) * -1;

			}
			//printClause(clause);
			solver.addClause(new VecInt(clause));
		}
		else {
			//Should be handled before this level
		}
		
	}
	
	private static boolean [] toBooleanArray (int i, int length) {
		boolean result[] = new boolean [length];
		int j = i;
		int index = 0;
		while (j > 0) {
			if (j % 2 == 0) {
				result[index] = false;
			}
			else {
				result[index] = true;
			}
			j = j / 2;
			index ++;
		}
		return result;
	}
	
	private static void handleEdgeStartsWith (Edge e) throws ContradictionException{
		//If constant
		
		if (e.getDest().getLength() > e.getSource().getLength()) {
			throw new RuntimeException ("Preprocesser fudged up " + e.getDest().getName() + ".length [" + e.getDest().getLength() + "] > " + e.getSource().getName() + ".length [" + e.getSource().getLength() + "]");
		}
		else if (e.getDest().getLength() == e.getSource().getLength()) {
			handleEdgeEqual(e);
		}
		
		int vector1 = retrieveInt(e.getSource());
		if (e.getDest().isConstant()) {
			for (int i = 0; i < e.getDest().getLength(); i++) {
				int clause[] = new int [1];
				int val = e.getDest().getSolution().charAt(i) - SymbolicStringConstraintsGeneral.MIN_CHAR;
				clause[0] = vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + val;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
		}
		else {
			int vector2 = retrieveInt(e.getDest());
			
			int length = e.getDest().getLength();
			
			int vectorLength = length * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			int clause[] = new int[2];
			//println ("Startswith start...");
			for (int i = 0; i < vectorLength; i++) {
				clause[0] = (vector1 + i) * -1;
				clause[1] = vector2 + i;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
				clause[0] = vector1 + i;
				clause[1] = (vector2 + i) * -1;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
			//println ("Startswith end");
			////println ("[handleStartsWith] " + e.getDest() + " should be constant");
			
		}
	}
	
	private static void handleEdgeEndsWith (Edge e) throws ContradictionException{
		//If constant
		
		if (e.getDest().getLength() > e.getSource().getLength()) {
			throw new RuntimeException ("Preprocesser fudged up");
		}
		else if (e.getDest().getLength() == e.getSource().getLength()) {
			handleEdgeEqual(e);
		}
		
		if (e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			vector1 = vector1 + ((e.getSource().getLength() - e.getDest().getLength()) * SymbolicStringConstraintsGeneral.DIFF_CHAR);
			for (int i = 0; i < e.getDest().getLength(); i++) {
				int clause[] = new int [1];
				int val = e.getDest().getSolution().charAt(i) - SymbolicStringConstraintsGeneral.MIN_CHAR;
				clause[0] = vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + val;
				//printClause(clause);
				solver.addClause(new VecInt(clause));
			}
		}
		else {
			//println ("[handleStartsWith] " + e.getDest() + " should be constant");
		}
	}
	
	private static void handleEdgeNotStartsWith (Edge e) throws ContradictionException{
		//If constant
		// When excluding "abc", I shouldn't exclude "ab"
		if (!e.getSource().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
		}
		if (!e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getDest());
		}
	}
	
	private static void handleEdgeNotEndsWith (Edge e) throws ContradictionException{
		//If constant
		// When excluding "abc", I shouldn't exclude "ab"
		if (!e.getSource().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
		}
		if (!e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getDest());
		}
	}
	
	private static void handleEdgeIndexof (EdgeIndexOf e) throws ContradictionException {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			int vector2 = retrieveInt(e.getDest());
			
			int lengthOfSource = e.getSource().getLength();
			int lengthOfDest = e.getDest().getLength();
			
			int vectorLengthOfSource = lengthOfSource * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			int vectorLengthOfDest = lengthOfDest * SymbolicStringConstraintsGeneral.DIFF_CHAR;
			
			int pos = e.getIndex().solutionInt();
			if (pos > -1) {
				int vectorPos = pos * SymbolicStringConstraintsGeneral.DIFF_CHAR;
				//println ("[handleEdgeIndexOf] start...");
				for (int i = vectorPos; i < vectorPos + vectorLengthOfDest; i++) {
					int clause[] = new int [2];
					clause[0] = vector1 + i;
					clause[1] = (vector2 + (i - vectorPos)) * -1;
					//printClause(clause);
					solver.addClause(new VecInt(clause));
					clause[0] = (vector1 + i) * -1;
					clause[1] = vector2 + (i - vectorPos);
					//printClause(clause);
					solver.addClause(new VecInt(clause));
					
				}
				//println ("[handleEdgeIndexOf] end");
			}
			else {
				//Must be dealt with lazily
			}
		}
		else if (!e.getSource().isConstant()) {
			int vector1 = retrieveInt(e.getSource());
			int length = e.getSource().getLength();
			String constant = e.getDest().getSolution();
			int position = e.getIndex().solutionInt();
			if (position >= 0) {
				//The string should be found at position
				int clause[] = new int [1];
				char c;
				int offset;
				for (int i = position; i < position + e.getDest().getLength(); i++) {
					c = constant.charAt(i - position);
					offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
					clause[0] = vector1 + i * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
					//printClause (clause);
					solver.addClause(new VecInt(clause));
				}
			}
			else {
				//The string must not be present anywhere
				int clause[] = new int [constant.length()];
				char c;
				int offset;
				for (int i = 0; i < e.getSource().getLength() - constant.length(); i++) {
					for (int j = i; j < i + constant.length(); j++) {
						c = constant.charAt(j - i);
						offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
						clause[j-i] = (vector1 + j * SymbolicStringConstraintsGeneral.DIFF_CHAR + offset) * -1;
					}
					//printClause(clause);
					solver.addClause(new VecInt(clause));

				}
			}
		}
		else if (!e.getDest().isConstant()) {
			int vector2 = retrieveInt(e.getDest());
			String constantSource = e.getSource().getSolution();
			//println ("[handleEdgeIndexof] constantSource: " + constantSource);
			int pos = e.getIndex().solutionInt();
			if (pos != -1) {
				//println ("[handleEdgeIndexOf] pos = " + pos);
				List<int[]> clauses = new ArrayList<int[]>();
				//println ("[handleEdgeIndexof] And clauses:");
				int[] tempClause = new int [1];
				char c;
				int offset;
				for (int j = pos; j < pos + e.getDest().getLength(); j++) {
					c = constantSource.charAt(j);
					offset = c - SymbolicStringConstraintsGeneral.MIN_CHAR;
					tempClause[0] = vector2 + (j - pos)* SymbolicStringConstraintsGeneral.DIFF_CHAR + offset;
					//printClause(tempClause);
					solver.addClause(new VecInt(tempClause));
				}
			}
			else {
				//Do this lazily
			}
			
		}
		else {
			throw new RuntimeException ("Preprocessor should handle this");
		}
	}
}

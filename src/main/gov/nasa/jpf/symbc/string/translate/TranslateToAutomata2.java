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
import java.util.Stack;
import java.util.Map.Entry;


import dk.brics.automaton.Automaton;
import dk.brics.string.stringoperations.Substring;
import dk.brics.string.stringoperations.Trim;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.string.AutomatonExtra;
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;
import gov.nasa.jpf.symbc.string.graph.Edge;
import gov.nasa.jpf.symbc.string.graph.EdgeCharAt;
import gov.nasa.jpf.symbc.string.graph.EdgeConcat;
import gov.nasa.jpf.symbc.string.graph.EdgeContains;
import gov.nasa.jpf.symbc.string.graph.EdgeEndsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOf;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOf2;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOfChar;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOfChar2;
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

public class TranslateToAutomata2 {
	
	/* For timing purposes */
	private static long duration;
	
	/* Keeps record of the automata at each vertex */
	private static Map<Vertex, Automaton> mapAutomaton;
	
	/* Global variables */
	private static StringGraph global_graph;
	private static PathCondition global_pc;
	private static boolean global_change; //If flagged, the graph has changed
	
	/* Handle unsat paths */
	private static Stack<LogicalORLinearIntegerConstraints> unsatStack1;
	private static Stack<LinearIntegerConstraint> unsatStack2;
	
	/* For not handling */
	private static List<Edge> notEdges;
	private static Map<Vertex, List<String>> concreteMap;
	private static Map<Vertex, Integer> mapVertexInteger;
	
	/* Debugging */
	private static String debug_unsat_reason;
	
	/* For integer solving */
	private static SymbolicConstraintsGeneral scg;
	
	public static boolean isSat (StringGraph g, PathCondition pc) {
		//println ("Running with the new Automata solvers");
		long starttime = System.currentTimeMillis();
		boolean result = inner_isSat(g, pc);
		duration = duration + (System.currentTimeMillis() - starttime);
		return result;
	}
	
	private static boolean inner_isSat (StringGraph g, PathCondition pc) {
		mapAutomaton = null;
		global_graph = g;
		global_pc  = pc;
		
		//println ("[isSat] integer constraints: " + pc.header);
		boolean restart = true;
		boolean interchangeNeeded;
		
		resetAutomata();
		
		while (restart) {
			//println ("[restart]: " + pc.toString());
			//println ("restart");
			/* check if there was a timeout */
			SymbolicStringConstraintsGeneral.checkTimeOut();
			
			restart = false;
			interchangeNeeded = false;
			
			
			//Initialise global variables
			unsatStack1 = new Stack<LogicalORLinearIntegerConstraints>();
			unsatStack2 = new Stack<LinearIntegerConstraint>();
			scg = new SymbolicConstraintsGeneral();
			
			
			
			//Iterate through graph (excluding nots) until convergence
			//println("Iterate through graph (excluding nots) until convergence");
			boolean result;
			for (Edge e: g.getEdges()) {
				//println ("Edge: " + e);
				result = handleEdge(e);
				if (result == false) {
					//Walked into unsat
					interchangeNeeded = true;
					break;
				}
			}
			//println ("Done iteration, interchange needed: " + interchangeNeeded);
			
			if (!interchangeNeeded) {
				/* If converging hasn't happened, restart */
				//println ("If converging hasn't happened, restart");
				if (global_change) {
					//println ("Have not converged yet");
					global_change = false;
					restart = true;
					//println ("converging...");
					continue;
				}
				//println ("Converged");
				//Iterate through nots
				//println ("Iterate through nots");
				notEdges = new ArrayList<Edge>();
				concreteMap = new HashMap<Vertex, List<String>>();
				mapVertexInteger = new HashMap<Vertex, Integer>();
				
				/* Easy nots */
				//println ("Easy nots");
				for (Edge e: g.getEdges()) {
					result = handleNotEdge (e);
					if (result == false) {
						interchangeNeeded = true;
						break;
					}
				}
				//println ("Done with easy nots, interchange needed: " + interchangeNeeded);
				
				if (!interchangeNeeded) {
					//println ("Hard nots");
					/* Hard nots */
					result = handleVarVarNots();
					if (result == false) {
						interchangeNeeded = true;
					}
					//println ("Done hard nots, interchange needed: " + interchangeNeeded);
				}
			}
			
			//Interchange
			if (interchangeNeeded) {
				//println ("Interchange");
				interchangeNeeded = false;
				LogicalORLinearIntegerConstraints resultloic = new LogicalORLinearIntegerConstraints();
				for (LogicalORLinearIntegerConstraints temploic: unsatStack1) {
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
				for (LinearIntegerConstraint lic: unsatStack2) {
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
				pc._addDet(resultloic);
				//println ("Adding: " + resultloic);
				
				if (PathCondition.flagSolved == false) {
					//println ("[isSat] Path Condition changed, starting integer solver...");
					long startTime = System.currentTimeMillis();
					boolean int_result = scg.isSatisfiable(pc);
					long temp_dur = (System.currentTimeMillis() - startTime);
					//int_duration = int_duration + temp_dur;
					duration -= temp_dur;
					if (int_result) {
						//println ("[isSat] Found to be sat, solving...");
						scg.solve(pc);
						PathCondition.flagSolved = true;
						//println ("[isSat] solved " + global_pc.header.toString());
						unsatStack1 = new Stack<LogicalORLinearIntegerConstraints>();
						unsatStack2 = new Stack<LinearIntegerConstraint>();

						return inner_isSat (g, pc); //remove recursion
					}
					else {
						//println ("[isSat] integer solver could not solve");
						//println ("[isSat] string expr: " + expr.toString());
						//println ("[isSat] not solved: " + global_pc.header.toString());
						return false;
					}
				}
				else {
					//println ("No change to path condition");
					return false;
				}
			}
		}
		return true;
	}
	
	private static void resetAutomata () {
		//println ("reseting...");
		//Enforce length on each automata
		mapAutomaton = new HashMap<Vertex, Automaton>();
		Automaton newAutomaton;
		for (Vertex v: global_graph.getVertices()) {
			if (v.isConstant()) {
				newAutomaton = Automaton.makeString(v.getSolution());
			} else {
				Automaton length = AutomatonExtra.lengthAutomaton(v.getLength());
				newAutomaton = AutomatonExtra.makeAnyStringFixed().intersection(length);
				v.setSolution(newAutomaton.getShortestExample(true));
			}
			mapAutomaton.put(v, newAutomaton);
		}
	}
	
	private static boolean handleEdge (Edge e) {
		//println ("[handleEdge] edge: " + e);
		boolean result = true;
		if (e instanceof EdgeStartsWith) {
			result = handleEdgeStartsWith((EdgeStartsWith) e);
		} else if (e instanceof EdgeEndsWith) { 
			result = handleEdgeEndsWith((EdgeEndsWith) e);
		} else if (e instanceof EdgeContains) {
			result = handleEdgeContains ((EdgeContains) e);
		} else if (e instanceof EdgeTrimEqual) {
			result = handleEdgeTrim ((EdgeTrimEqual) e);
		} else if (e instanceof EdgeConcat) {
			result = handleEdgeConcat ((EdgeConcat) e);
		} else if (e instanceof EdgeIndexOf) {
			result = handleEdgeIndexOf ((EdgeIndexOf) e);
		} else if (e instanceof EdgeIndexOf2) {
			result = handleEdgeIndexOf2 ((EdgeIndexOf2) e);
		} else if (e instanceof EdgeIndexOfChar) {
			result = handleEdgeIndexOfChar ((EdgeIndexOfChar) e);
		} else if (e instanceof EdgeIndexOfChar2) {
			result = handleEdgeIndexOfChar2 ((EdgeIndexOfChar2) e);
		} else if (e instanceof EdgeCharAt) {
			result = handleEdgeCharAt ((EdgeCharAt) e);
		} else if (e instanceof EdgeNotCharAt) { //Need to explain why this is not part of not handling
			result = handleEdgeNotCharAt ((EdgeNotCharAt) e);
		} else if (e instanceof EdgeSubstring1Equal) {
			result = handleEdgeSubstring1Equal ((EdgeSubstring1Equal) e);
		} else if (e instanceof EdgeSubstring2Equal) {
			result = handleEdgeSubstring2Equal ((EdgeSubstring2Equal) e);
		} else if (e instanceof EdgeLastIndexOfChar) {
			result = handleEdgeLastIndexOfChar ((EdgeLastIndexOfChar) e);
		} else if (e instanceof EdgeLastIndexOfChar2) {
			result = handleEdgeLastIndexOfChar2 ((EdgeLastIndexOfChar2) e);
		} else if (e instanceof EdgeNotEqual) {
			//Not handled here
		} else if (e instanceof EdgeNotStartsWith) {
			//Not handled here
		} else if (e instanceof EdgeNotEndsWith) {
			//Not handled here
		} else if (e instanceof EdgeNotContains) {
			//Not handled here
		} else {
			throw new RuntimeException ("Edge not understood");
		}
		if (result == false) {
			//println ("debug_unsat_reason: " + debug_unsat_reason);
		}
		return result;
	}
	
	private static boolean handleEdgeStartsWith (EdgeStartsWith e) {
		//println ("[handleEdgeStartsWith] e: " + e);
		unsatStack1.add(excludeVertecis(e));
		
		boolean a1Changed, a2Changed;
		a1Changed = false; a2Changed = false;
		
		Automaton origSource = mapAutomaton.get(e.getSource());
		Automaton origDest = mapAutomaton.get(e.getDest());
		
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest()).concatenate(AutomatonExtra.makeAnyStringFixed());
		
		//println ("[handleEdgeStartsWith] a1 example: '" + a1.getShortestExample(true) + "'");
		//println ("[handleEdgeStartsWith] a2 example: '" + a2.getShortestExample(true) + "'");
		
		Automaton intersection = AutomatonExtra.intersection(a1, a2);
		if (intersection.isEmpty()) {
			debug_unsat_reason = "In handleEdgeStartsWith, source intersection was empty";
			return false;
		}
		
		if (!origSource.equals(intersection)) {a1Changed = true;}
		mapAutomaton.put(e.getSource(), intersection);
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
		
		Automaton temp = AutomatonExtra.startingSubstrings(intersection);
		Automaton intersection2 = AutomatonExtra.intersection(temp, origDest);
		//println ("[handleEdgeStartsWith] intersection2 example: '" + intersection2.getShortestExample(true) + "'"); 
		if (intersection2.isEmpty()) {
			debug_unsat_reason = "In handleEdgeStartsWith, destination intersection was empty";
			return false;
		}
		if (!origDest.equals(intersection2)) {a2Changed = true;}
		mapAutomaton.put(e.getDest(), intersection2);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
		
		if (a1Changed || a2Changed) {
			//println (String.format("handleEdgeStartswith has changed something %b, %b", a1Changed, a2Changed));
			global_change = true;
		}
		return true;
	}
	
	private static boolean handleEdgeEndsWith (EdgeEndsWith e) {
		//println ("[handleEdgeEndsWith] entered");
		unsatStack1.add(excludeVertecis(e));
		
		Automaton origSource = mapAutomaton.get(e.getSource());
		Automaton origDest = mapAutomaton.get(e.getDest());
		
		Automaton source = mapAutomaton.get(e.getSource());
		Automaton dest = mapAutomaton.get(e.getDest());
		
		boolean sourceChanged = false, destChanged = false;
		
		Automaton newSource = AutomatonExtra.intersection(source, AutomatonExtra.makeAnyStringFixed().concatenate(dest));
		if (newSource.isEmpty()) {
			debug_unsat_reason = "In handleEdgeEndsWith, source intersection was empty";
			return false;
		}
		if (!newSource.equals(origSource)) {sourceChanged = true;}
		mapAutomaton.put(e.getSource(), newSource);
		if (!e.getSource().isConstant()) e.getSource().setSolution(newSource.getShortestExample(true));
		
		Automaton newDest = AutomatonExtra.intersection(dest, AutomatonExtra.endingSubstrings(source));
		if (newDest.isEmpty()) {
			debug_unsat_reason = "In handleEdgeEndsWith, destination intersection was empty";
			return false;
		}
		if (!newDest.equals(origDest)) {destChanged = true;}
		mapAutomaton.put(e.getDest(), newDest);
		if (!e.getDest().isConstant()) e.getDest().setSolution(newDest.getShortestExample(true));
		
		if (sourceChanged || destChanged) {
			global_change = true;
		}
		return true;
	}
	
	private static boolean handleEdgeContains (EdgeContains e) {
		//println ("[handleEdgeContains] e:" + e);
		unsatStack1.add(excludeVertecis(e));
		
		Automaton origSource = mapAutomaton.get(e.getSource());
		Automaton origDest = mapAutomaton.get(e.getDest());
		
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		
		Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
		Automaton intersection = AutomatonExtra.intersection(a1, temp);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeContains] a1 example: '" + a1.getShortestExample(true) + "'");
			//println ("[handleEdgeContains] a2 example: '" + a2.getShortestExample(true) + "'");
			//println ("[handleEdgeContains] temp example: '" + temp.getShortestExample(true) + "'");
			debug_unsat_reason = "In handleEdgeContains, source intersection was empty";
			return false;
		}
		boolean a1Changed = false;
		if (!origSource.equals(intersection)) {a1Changed = true;}
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
		mapAutomaton.put(e.getSource(), intersection);
		
		Automaton subsets = new Substring().op(a1);
		intersection = AutomatonExtra.intersection(a2, subsets);
		if (intersection.isEmpty()) {
			debug_unsat_reason = "In handleEdgeContains, destination intersection was empty";
			return false;
		}
		boolean a2Changed = false;
		if (!origDest.equals(intersection)) {a2Changed = true;}
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection.getShortestExample(true));
		mapAutomaton.put(e.getDest(), intersection);

		if (a1Changed || a2Changed) {
			global_change = true;
		}
		return true;
	}
	
	private static boolean handleEdgeTrim (EdgeTrimEqual e) {
		unsatStack1.add(excludeVertecis(e));
		
		Automaton origSource = mapAutomaton.get(e.getSource());
		Automaton origDest = mapAutomaton.get(e.getDest());
		
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		
		Automaton temp = new Trim().op(a1);
		temp = AutomatonExtra.minus(temp, Automaton.makeEmptyString());
		Automaton intersection = AutomatonExtra.intersection(a2, temp);
		if (intersection.isEmpty()) {
			debug_unsat_reason = "In handleEdgeTrim, source intersection was empty";
			return false;
		}
		boolean a2Changed = false;
		if (!origDest.equals(intersection)) a2Changed = true;
		mapAutomaton.put (e.getDest(), intersection);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection.getShortestExample(true));
		
		Automaton temp2 = AutomatonExtra.star(Automaton.makeCharRange((char) 32, (char) 127)).concatenate(intersection).concatenate(AutomatonExtra.star(Automaton.makeCharRange((char) 32, (char) 127)));
		Automaton intersection2 = AutomatonExtra.intersection(a1, temp2);
		if (intersection2.isEmpty()) {
			debug_unsat_reason = "In handleEdgeTrim, destination intersection was empty";
			return false;
		}
		boolean a1Changed = false;
		if (!origSource.equals(intersection2)) a1Changed = true;
		mapAutomaton.put(e.getSource(), intersection2);
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection2.getShortestExample(true));
		
		if (a1Changed || a2Changed) {
			global_change = true;
		}
		
		return true;
	}
	
	private static boolean handleEdgeConcat (EdgeConcat e) {
		unsatStack1.add(excludeVertecis(e));
		
		Automaton origSource0 = mapAutomaton.get(e.getSources().get(0));
		Automaton origSource1 = mapAutomaton.get(e.getSources().get(1));
		Automaton origDest = mapAutomaton.get(e.getDest());
		
		Automaton a1 = mapAutomaton.get(e.getSources().get(0));
		Automaton a2 = mapAutomaton.get(e.getSources().get(1));
		Automaton a3 = mapAutomaton.get(e.getDest());
		
		//TODO remove concatenations with empty strings while preprocessing the constraint
		if(a1.isEmptyString() || a2.isEmptyString()) { //concatenation with empty string
			return true;
		}
		
		boolean a3changed = false;
		Automaton concatA = a1.concatenate(a2);
		Automaton intersection = AutomatonExtra.intersection(concatA, a3);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeConcat] intersection is empty");
			debug_unsat_reason = "In handleEdgeConcat, destination intersection was empty";
			return false;
		}
		if (!origDest.equals(intersection)) a3changed = true;
		mapAutomaton.put(e.getDest(), intersection);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection.getShortestExample(true));
		
		boolean a1changed = false;
		Automaton temp = AutomatonExtra.substring(intersection, 0, e.getSources().get(0).getLength());
		Automaton intersection2 = AutomatonExtra.intersection(a1, temp);
		if (intersection2.isEmpty()) {
			//println ("[handleEdgeConcat] intersection2 is empty");
			debug_unsat_reason = "In handleEdgeConcat, source 0 intersection was empty";
			return false;
		}

		if (!origSource0.equals(intersection2)) a1changed = true;
		mapAutomaton.put(e.getSources().get(0), intersection2);
		if (!e.getSources().get(0).isConstant()) e.getSources().get(0).setSolution(intersection2.getShortestExample(true));
		
		boolean a2changed = false;
		temp = AutomatonExtra.substring(intersection, e.getSources().get(0).getLength());
		Automaton intersection3 = AutomatonExtra.intersection(a2, temp);
		if (intersection3.isEmpty()) {
			//println ("[handleEdgeConcat] intersection3 is empty");
			debug_unsat_reason = "In handleEdgeConcat, source 1 intersection was empty";
			return false;
		}

		if (!origSource1.equals(intersection3)) a2changed = true;
		mapAutomaton.put(e.getSources().get(1), intersection3);
		if (!e.getSources().get(1).isConstant()) e.getSources().get(1).setSolution(intersection3.getShortestExample(true));
		
		if (a1changed || a2changed || a3changed) {
			global_change = true;
		}
		
		return true;
		
	}
	
	private static boolean handleEdgeIndexOf (EdgeIndexOf e) {
		LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		unsatStack1.add(loic);
		
		Automaton origSource = mapAutomaton.get(e.getSource());
		Automaton origDest = mapAutomaton.get(e.getDest());
		
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		
		boolean a1Changed, a2Changed = false;
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "In handleEdgeIndexOf, return false 1";
				return false;
			}
			//Make sure the destination is not present in source before index.
			//TODO: Opportunity to set things right (this is wrong)
			/*Automaton exclude = Automaton.makeEmpty();
			for (int i = 0; i < index; i++) {
				Automaton prefixSpaces = AutomatonExtra.lengthAutomaton(i);
				Automaton aNew = prefixSpaces.concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
				//println (String.format("[handleEdgeIndexOf] aNew: '%s'", aNew.getShortestExample(true)));
				exclude = exclude.union(aNew);
			}
			//Lengthen exclude
			Automaton lengthenExclude = exclude.concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton excludeInverse = lengthenExclude.complement().intersection(AutomatonExtra.makeAnyStringFixed());
			excludeInverse = AutomatonExtra.intersection(excludeInverse, AutomatonExtra.lengthAutomaton(e.getSource().getLength()));
			a1 = AutomatonExtra.intersection(a1, excludeInverse);
			if (a1.isEmpty()) {
				debug_unsat_reason = "In handleEdgeIndexOf, return false 2";
				return false;
			}*/
			if (!origSource.equals(a1)) {a1Changed = true;}
			mapAutomaton.put(e.getSource(), a1);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
						
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "In handleEdgeIndexOf, return false 3";
				return false;
			}
			else {
				a1Changed = false; a2Changed = false;
				if (!origSource.equals(intersection)) a1Changed = true;
				
				Automaton temp2 = AutomatonExtra.substring(intersection, index, index + e.getDest().getLength());
				Automaton intersection2 = AutomatonExtra.intersection(a2, temp2);
				if (intersection2.isEmpty()) {
					debug_unsat_reason = "In handleEdgeIndexOf, return false 3";
					return false;
				}
				if (!origDest.equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				
				if (a1Changed || a2Changed) {
					global_change = true;
				}
				
				return true;
			}
		}
		else {
			//Handle in nots
			return true;
		}
	}

	private static boolean handleEdgeIndexOf2 (EdgeIndexOf2 e) {
		LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getMinIndex(), Comparator.NE, new IntegerConstant(e.getIndex().getMinIndex().solution())));
		unsatStack1.add(loic);
		
		//println ("[handleEdgeIndexOf2] entered: " + e.getName());
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		//First check if it is possible
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeIndexOf] indexof could not be found anywhere, forcing index == -1 or longer length for " + e.getSource().getName();
				return false;
			}
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			//println ("[handleEdgeIndexOf] intersection example: " + intersection.getShortestExample(true));
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeIndexOf] 1. indexof could not be applyied at the current place";
				return false;
			}
			else {
				boolean a1Changed, a2Changed;
				a1Changed = false; a2Changed = false;
				if (!a1.equals(intersection)) a1Changed = true;
				
				Automaton temp2 = AutomatonExtra.substring(intersection, index, index + e.getDest().getLength());
				//println ("[handleEdgeIndexOf] temp2 example: '" + temp2.getShortestExample(true) + "'");
				Automaton intersection2 = AutomatonExtra.intersection(a2, temp2);
				if (intersection2.isEmpty()) {
					debug_unsat_reason = "[handleEdgeIndexOf] 2. indexof could not be applyied at the current place";
					return false;
				}
				if (!a2.equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				
				if (a1Changed || a2Changed) {
					global_change = true;
				}
				
				return true;
			}
		}
		else {
			//handle in handleNots
			return true;
		}
	}
	
	private static boolean handleEdgeIndexOfChar (EdgeIndexOfChar e) {
		//println ("handleEdgeIndexOfChar entered");
		LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		unsatStack1.add(loic);
		Automaton a1 = mapAutomaton.get(e.getSource());
		int index = e.getIndex().solutionInt();
		String character = String.valueOf((char) e.getIndex().getExpression().solution());
		if (index > -1) {
			//println ("[handleEdgeIndexOfChar] index > -1");
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			//println ("Character: " + (e.getIndex().getExpression().solution()));
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeIndexOfChar] 1. indexof '" + character + "' could not be found anywhere, forcing index == -1 or longer lengths";
				return false;
			}
			
			Automaton exclude = Automaton.makeEmpty();
			for (int i = 0; i <= index - e.getDest().getLength(); i++) {
				Automaton prefixSpaces = AutomatonExtra.lengthAutomaton(i);
				Automaton suffixSpaces = AutomatonExtra.lengthAutomaton(index - i - e.getDest().getLength());
				Automaton aNew = prefixSpaces.concatenate(Automaton.makeChar(character.charAt(0))).concatenate(suffixSpaces);
				//println (String.format("[handleEdgeIndexOf] aNew: '%s'", aNew.getShortestExample(true)));
				exclude = exclude.union(aNew);
			}
			Automaton lengthenExclude = exclude.concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton excludeInverse = lengthenExclude.complement().intersection(AutomatonExtra.makeAnyStringFixed());
			excludeInverse = AutomatonExtra.intersection(excludeInverse, AutomatonExtra.lengthAutomaton(e.getSource().getLength()));
			a1 = AutomatonExtra.intersection(a1, excludeInverse);
			if (a1.isEmpty()) {
				debug_unsat_reason = "[handleEdgeIndexOf] String encountered before";
				return false;
			}
			mapAutomaton.put(e.getSource(), a1);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
			
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeIndexOfChar] 2. indexof at " + index + " could not be applyied at the current place ('" + e.getSource().getSolution() + "', '" + e.getDest().getSolution()+ "')";
				return false;
			}
			else {
				//println ("[handleEdgeIndexOfChar] all going good");
				boolean a1Changed, a2Changed;
				a1Changed = false; a2Changed = false;
				if (!a1.equals(intersection)) a1Changed = true;
				
				Automaton temp2 = AutomatonExtra.substring(intersection, index, index + e.getDest().getLength());
				Automaton intersection2 = AutomatonExtra.intersection(Automaton.makeString(character), temp2);
				if (intersection2.isEmpty()) {
					debug_unsat_reason = "[handleEdgeIndexOf] 3. indexof could not be applyied at the current place";
					return false;
				}
				if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				if (a1Changed || a2Changed) {
					global_change = true;
				}
				return true;
			}
		}
		else {
			//println ("[handleEdgeIndexOfChar] handle later");
			//Handle later
			return true;
		}
	}
	
	private static boolean handleEdgeLastIndexOfChar (EdgeLastIndexOfChar e) {
		//println ("[EdgeLastIndexOfChar] e: " + e);
		//println ("[EdgeLastIndexOfChar] e.getIndex(): " + e.getIndex().solution());
		//println ("[EdgeLastIndexOfChar] e.getIndex().getExpression(): " + e.getIndex().getExpression().solution());
		LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		unsatStack1.add(loic);
		
		Automaton a1 = mapAutomaton.get(e.getSource());
		int index = e.getIndex().solutionInt();
		String character = String.valueOf((char) e.getIndex().getExpression().solution());
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeLastIndexOfChar] 1.indexof could not be found anywhere, forcing index == -1 or longer length for " + e.getSource().getName();	
				return false;
			}
			temp = AutomatonExtra.lengthAutomaton(index);
			Automaton lastPieceOfString = Automaton.makeCharRange((char) SymbolicStringConstraintsGeneral.MIN_CHAR, (char) SymbolicStringConstraintsGeneral.MAX_CHAR);
			lastPieceOfString = lastPieceOfString.minus(Automaton.makeChar(character.charAt(0)));
			lastPieceOfString = AutomatonExtra.star(lastPieceOfString);
			//Need to concatenate with any string that does not contain this character.
			temp = temp.concatenate(Automaton.makeString(character)).concatenate(lastPieceOfString);
			intersection = AutomatonExtra.intersection(a1, temp);
			//println ("[handleEdgeIndexOf] intersection example: " + intersection.getShortestExample(true));
			if (intersection.isEmpty()) {
				debug_unsat_reason =  "[handleEdgeLastIndexOfChar] 2. indexof could not be applyied at the current place";
				return false;
			}
			else {
				boolean a1Changed, a2Changed;
				a1Changed = false; a2Changed = false;
				if (!a1.equals(intersection)) a1Changed = true;
				
				Automaton temp2 = AutomatonExtra.substring(intersection, index, index + e.getDest().getLength());
				//println ("[handleEdgeIndexOf] temp2 example: '" + temp2.getShortestExample(true) + "'");
				Automaton intersection2 = AutomatonExtra.intersection(Automaton.makeString(character), temp2);
				if (intersection2.isEmpty()) {
					debug_unsat_reason = "[handleEdgeLastIndexOfChar] 3. indexof could not be applyied at the current place";
					return false;
				}
				if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				
				if (a1Changed || a2Changed) {
					global_change = true;
				}
				
				return true;
			}
		}
		else {
			//handle in handleNots
			return true;
		}
	}
	
	private static boolean handleEdgeLastIndexOfChar2 (EdgeLastIndexOfChar2 e) {
		LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(e.getIndex().getMinDist().solution())));
		unsatStack1.add(loic);
		
		
		//println ("[handleEdgeLastIndexOfChar2] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		//Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		String character = String.valueOf((char) e.getIndex().getExpression().solution());
		//First check if it is possible
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeLastIndexOfChar] 1.indexof could not be found anywhere, forcing index == -1 or longer length for " + e.getSource().getName();
				
				return false;
			}
			temp = AutomatonExtra.lengthAutomaton(index);
			Automaton lastPieceOfString = Automaton.makeCharRange((char) SymbolicStringConstraintsGeneral.MIN_CHAR, (char) SymbolicStringConstraintsGeneral.MAX_CHAR);
			lastPieceOfString = lastPieceOfString.minus(Automaton.makeChar(character.charAt(0)));
			lastPieceOfString = AutomatonExtra.star(lastPieceOfString);
			lastPieceOfString = lastPieceOfString.concatenate(AutomatonExtra.lengthAutomaton(e.getIndex().getMinDist().solutionInt() - e.getIndex().solutionInt() + 1));
			//Need to concatenate with any string that does not contain this character.
			temp = temp.concatenate(Automaton.makeString(character)).concatenate(lastPieceOfString).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			//println ("[handleEdgeIndexOf] intersection example: " + intersection.getShortestExample(true));
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeLastIndexOfChar] 2. indexof could not be applyied at the current place";
				return false;
			}
			else {
				boolean a1Changed, a2Changed;
				a1Changed = false; a2Changed = false;
				if (!a1.equals(intersection)) a1Changed = true;
				
				Automaton temp2 = AutomatonExtra.substring(intersection, index, index + e.getDest().getLength());
				//println ("[handleEdgeIndexOf] temp2 example: '" + temp2.getShortestExample(true) + "'");
				Automaton intersection2 = AutomatonExtra.intersection(Automaton.makeString(character), temp2);
				if (intersection2.isEmpty()) {
					debug_unsat_reason = "[handleEdgeLastIndexOfChar] 3. indexof could not be applyied at the current place";
					return false;
				}
				if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				
				if (a1Changed || a2Changed) {
					global_change = true;
				}
				
				return true;
			}
		}
		else {
			
			//handle in handleNots
			return true;
		}
		//return true;
	}

	private static boolean handleEdgeIndexOfChar2 (EdgeIndexOfChar2 e) {
		LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(e.getIndex().getMinDist().solution())));
		unsatStack1.add(loic);
		Automaton a1 = mapAutomaton.get(e.getSource());
		int index = e.getIndex().solutionInt();
		String character = String.valueOf((char) e.getIndex().getExpression().solution());
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeIndexOfChar] 1. indexof '" + character + "' could not be found anywhere, forcing index == -1 or longer lengths";
				return false;
			}
			
			Automaton exclude = Automaton.makeEmpty();
			for (int i = e.getIndex().getMinDist().solutionInt(); i <= index - e.getDest().getLength(); i++) {
				Automaton prefixSpaces = AutomatonExtra.lengthAutomaton(i);
				Automaton suffixSpaces = AutomatonExtra.lengthAutomaton(index - i - e.getDest().getLength());
				Automaton aNew = prefixSpaces.concatenate(Automaton.makeChar(character.charAt(0))).concatenate(suffixSpaces);
				exclude = exclude.union(aNew);
			}
			//TODO: Set right
			Automaton lengthenExclude = exclude.concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton excludeInverse = lengthenExclude.complement().intersection(AutomatonExtra.makeAnyStringFixed());
			excludeInverse = AutomatonExtra.intersection(excludeInverse, AutomatonExtra.lengthAutomaton(e.getSource().getLength()));
			a1 = AutomatonExtra.intersection(a1, excludeInverse);
			if (a1.isEmpty()) {
				debug_unsat_reason = "[handleEdgeIndexOf] String encountered before";
				return false;
			}
			mapAutomaton.put(e.getSource(), a1);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
			
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeIndexOfChar] 2. indexof at " + index + " could not be applyied at the current place ('" + e.getSource().getSolution() + "', '" + e.getDest().getSolution()+ "')";
				return false;
			}
			else {
				boolean a1Changed, a2Changed;
				a1Changed = false; a2Changed = false;
				if (!a1.equals(intersection)) a1Changed = true;
				
				Automaton temp2 = AutomatonExtra.substring(intersection, index, index + e.getDest().getLength());
				Automaton intersection2 = AutomatonExtra.intersection(Automaton.makeString(character), temp2);
				if (intersection2.isEmpty()) {
					debug_unsat_reason = "[handleEdgeIndexOf] 3. indexof could not be applyied at the current place";
					return false;
				}
				if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				if (a1Changed || a2Changed) {
					global_change = true;
				}
				return true;
			}
		}
		else {
			//Handle later
			return true;
		}
	}
	
	private static boolean handleEdgeCharAt (EdgeCharAt e) {
		LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
		loic.addToList(new LinearIntegerConstraint(e.getValue(), Comparator.NE, new IntegerConstant(e.getValue().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		unsatStack1.add(loic);
		
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = Automaton.makeChar((char) e.getValue().solution());
		Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
		Automaton intersection = AutomatonExtra.intersection(a1, temp);
		if (intersection.isEmpty()) {
			debug_unsat_reason = "[handleEdgeCharAt] 1. intersection empty, making index == -1 because the character could not be found anywhere";
			return false;
		}
		else {
			temp = AutomatonExtra.lengthAutomaton(e.getIndex().solutionInt());
			temp = temp.concatenate(Automaton.makeChar((char) e.getValue().solution()).concatenate(AutomatonExtra.makeAnyStringFixed()));
			intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeCharAt] 2. intersection empty, current index or value is not valid";
				return false;
			}
			else {
				boolean a1Changed = false;
				if (!intersection.equals(a1)) a1Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (a1Changed) {global_change = true;}
			}
		}
		return true;
	}
	
	private static boolean handleEdgeNotCharAt (EdgeNotCharAt e) {
		//println ("EdgeNotCharAt " + e.getValue().solution());
		LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
		loic.addToList(new LinearIntegerConstraint(e.getValue(), Comparator.NE, new IntegerConstant(e.getValue().solution())));
		loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		unsatStack1.add(loic);
		
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = Automaton.makeChar((char) e.getValue().solution());
		Automaton temp = AutomatonExtra.lengthAutomaton(e.getIndex().solutionInt());
		temp = temp.concatenate(Automaton.makeChar((char) e.getValue().solution()).concatenate(AutomatonExtra.makeAnyStringFixed()));
		//println ("temp example '" + temp.getShortestExample(true) +"'");
		Automaton intersection = a1.minus(temp);
		if (intersection.isEmpty()) {
			debug_unsat_reason = "[handleEdgeNotCharAt] 2. intersection empty, current index or value is not valid";
			return false;
		}
		else {
			boolean a1Changed = false;
			if (!intersection.equals(a1)) a1Changed = true;
			mapAutomaton.put(e.getSource(), intersection);
			if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
			if (a1Changed) {global_change = true;}
		}
		return true;
	}
	
	private static boolean handleEdgeSubstring1Equal (EdgeSubstring1Equal e) {
		//println ("[handleEdgeSubstring1Equal] e:" + e);
		if (e.isArgument1Symbolic()) {
			//println ("[handleEdgeSubstring1Equal] e.Arg1(): " + e.getArgument1Symbolic().solution());
		} else {
			//println ("[handleEdgeSubstring1Equal] e.Arg1(): " + e.getArgument1());
		}
		LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
		if (e.isArgument1Symbolic()) {
			loic.addToList(new LinearIntegerConstraint(e.getArgument1Symbolic(), Comparator.NE, new IntegerConstant(e.getArgument1Symbolic().solution())));
		}
		unsatStack1.add(loic);
		
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		
		Automaton temp = AutomatonExtra.substring(a1, e.getArgument1());
		//println ("[handleEdgeSubstring1Equal] substring example: '" + temp.getShortestExample(true) + "'");
		Automaton intersection = AutomatonExtra.intersection(temp, a2);
		//println ("[handleEdgeSubstring1Equal] intersection example: '" + intersection.getShortestExample(true) + "'");
		//println ("[handleEdgeSubstring1Equal] intersection example: '" + intersection.getStrings(1) + "'");
		if (intersection.isEmpty()) {
			debug_unsat_reason = "[handleEdgeSubstring1Equal] intersection empty";
			return false;
		}
		boolean a2Changed = false;
		if (!a2.equals(intersection)) a2Changed = true;
		mapAutomaton.put(e.getDest(), intersection);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection.getShortestExample(true));
		
		Automaton temp2 = Automaton.makeEmptyString();
		for (int i = 0; i < e.getArgument1(); i++) {
			temp2 = temp2.concatenate(Automaton.makeCharRange((char) 32 , (char) 127)); 
		}
		temp2 = temp2.concatenate(intersection);
		//println ("[handleEdgeSubstring1Equal] temp2 example: '" + temp2.getShortestExample(true) + "'");
		//println ("[handleEdgeSubstring1Equal] temp2 example: '" + temp2.getStrings(2) + "'");
		Automaton intersection2 = AutomatonExtra.intersection(a1, temp2);
		if (intersection2.isEmpty()) {
			debug_unsat_reason = "[handleEdgeSubstring1Equal] intersection empty";
			return false;
		}
		boolean a1Changed = false;
		if (!a1.equals(intersection2)) a1Changed = true;
		mapAutomaton.put(e.getSource(), intersection2);
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection2.getShortestExample(true));
		
		if (a1Changed || a2Changed) {
			global_change = true;
		}
		
		return true;
	}
	
	private static boolean handleEdgeSubstring2Equal (EdgeSubstring2Equal e) {
		Automaton source = mapAutomaton.get(e.getSource());
		Automaton dest = mapAutomaton.get(e.getDest());
		if (!e.hasSymbolicArgs()) {
			unsatStack1.add(excludeVertecis(e));
			Automaton temp = AutomatonExtra.substring(source, e.getArgument1(), e.getArgument2());
			Automaton intersection = AutomatonExtra.intersection(temp, dest);
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeSubstring2Equal] 1. intersection empty";
				return false;
			}
			boolean a2Changed = false;
			if (!dest.equals(intersection)) a2Changed = true;
			mapAutomaton.put(e.getDest(), intersection);
			if (!e.getDest().isConstant()) e.getDest().setSolution(intersection.getShortestExample(true));
			
			Automaton temp2 = Automaton.makeEmptyString();
			for (int i = 0; i < e.getArgument1(); i++) {
				temp2 = temp2.concatenate(Automaton.makeCharRange((char) 32 , (char) 127)); 
			}
			temp2 = temp2.concatenate(intersection).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection2 = AutomatonExtra.intersection(source, temp2);
			if (intersection2.isEmpty()) {
				debug_unsat_reason = "[handleEdgeSubstring2Equal] 2. intersection empty";
				return false;
			}
			boolean a1Changed = false;
			if (!source.equals(intersection2)) a1Changed = true;
			mapAutomaton.put(e.getSource(), intersection2);
			if (!e.getSource().isConstant()) e.getSource().setSolution(intersection2.getShortestExample(true));
			
			if (a1Changed || a2Changed) {
				global_change = true;
			}
			
			return true;
		}
		else if (e.getSymbolicArgument2() != null && e.getSymbolicArgument1() == null) {
			LogicalORLinearIntegerConstraints loic = excludeVertecis(e);
			loic.addToList(new LinearIntegerConstraint(e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(e.getSymbolicArgument2().solution())));
			unsatStack1.add(loic);
			
			int arg2 = e.getSymbolicArgument2().solutionInt();
			Automaton temp = AutomatonExtra.substring(source, e.getArgument1(), arg2);
			//println ("[handleEdgeSubstring2Equal] source.getLength() = " + e.getSource().getLength());
			//println ("[handleEdgeSubstring2Equal] temp diff = " + (arg2 - e.getArgument1()));
			Automaton intersection = AutomatonExtra.intersection(temp, dest);
			
			if (intersection.isEmpty()) {
				debug_unsat_reason = "[handleEdgeSubstring2Equal] 3. intersection empty";
				return false;
			}
			boolean a2Changed = false;
			if (!dest.equals(intersection)) a2Changed = true;
			mapAutomaton.put(e.getDest(), intersection);
			if (!e.getDest().isConstant()) e.getDest().setSolution(intersection.getShortestExample(true));
			
			Automaton temp2 = Automaton.makeEmptyString();
			for (int i = 0; i < e.getArgument1(); i++) {
				temp2 = temp2.concatenate(Automaton.makeCharRange((char) 32 , (char) 127)); 
			}
			temp2 = temp2.concatenate(intersection).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection2 = AutomatonExtra.intersection(source, temp2);
			if (intersection2.isEmpty()) {
				debug_unsat_reason = "[handleEdgeSubstring2Equal] 4. intersection empty";
				return false;
			}
			boolean a1Changed = false;
			if (!source.equals(intersection2)) a1Changed = true;
			mapAutomaton.put(e.getSource(), intersection2);
			if (!e.getSource().isConstant()) e.getSource().setSolution(intersection2.getShortestExample(true));
			
			if (a1Changed || a2Changed) {
				global_change = true;
			}
			
			return true;
		}
		else {
			throw new RuntimeException ("Not supported, yet");
		}
	}

	
	/* NOT HANDLING START */
	
	private static boolean handleNotEdge (Edge e) {
		boolean result = true;
		if (e instanceof EdgeNotEqual) {
			result = handleEdgeNotEqual (e);
		} else if (e instanceof EdgeNotStartsWith) {
			result = handleEdgeNotStartsWith (e);
		} else if (e instanceof EdgeNotEndsWith) {
			result = handleEdgeNotEndsWith (e);
		} else if (e instanceof EdgeNotContains) {
			result = handleEdgeNotContains (e);
		} else if (e instanceof EdgeIndexOf) {
			result = handleNotEdgeIndexOf ((EdgeIndexOf) e);
		} else if (e instanceof EdgeIndexOf2) {
			result = handleNotEdgeIndexOf2 ((EdgeIndexOf2) e);
		} else if (e instanceof EdgeIndexOfChar) {
			result = handleNotEdgeIndexOfChar ((EdgeIndexOfChar) e);
		} else if (e instanceof EdgeIndexOfChar2) {
			result = handleNotEdgeIndexOfChar2 ((EdgeIndexOfChar2) e);
		} else if (e instanceof EdgeLastIndexOfChar) {
			result = handleNotEdgeLastIndexOfChar ((EdgeLastIndexOfChar) e);
		} else if (e instanceof EdgeLastIndexOfChar2) {
			result = handleNotEdgeLastIndexOfChar2 ((EdgeLastIndexOfChar2) e);
		}
		//println ("handleNotEdge: " + e + " " + e.getClass() + ", result: " + result);
		if (result == false) {
			//println ("debug_unsat_reason: " + debug_unsat_reason);
		}
		return result; 
	}
	
	private static boolean handleEdgeNotEqual (Edge e) {
		/*if (!e.getSource().getSolution().equals(e.getDest().getSolution())) {
			return true;
		}*/
		
		if (e.getSource().getLength() != e.getDest().getLength()) {
			return true; //This should actually never be reached.
		}
		
		//Source == Dest
		if (e.getSource().isConstant() && !e.getDest().isConstant()) {
			unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			Automaton destination = mapAutomaton.get(e.getDest());
			String source = e.getSource().getSolution();
			destination = destination.minus(Automaton.makeString(source));
			if (destination.isEmpty()) {
				debug_unsat_reason = "Not handling of edge equals, with source constant, lead to empty destination";
				return false;
			}
			e.getDest().setSolution(destination.getShortestExample(true));
			mapAutomaton.put(e.getDest(), destination);
			global_change = true;
		} else if (!e.getSource().isConstant() && e.getDest().isConstant()) {
			unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			Automaton source = mapAutomaton.get(e.getSource());
			String destination = e.getDest().getSolution();
			source = source.minus(Automaton.makeString(destination));
			if (source.isEmpty()) {
				debug_unsat_reason = "Not handling of edge equals, with destination constant, lead to empty source";
				return false;
			}
			e.getSource().setSolution(source.getShortestExample(true));
			mapAutomaton.put(e.getSource(), source);
			global_change = true;
		} else if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			unsatStack1.add(excludeVertecis(e));
			notEdges.add(e);
		} else {
			//Everything is constant
			String source = e.getSource().getSolution();
			String dest = e.getDest().getSolution();
			return !source.equals(dest);
		}
		return true;
	}
	
	public static boolean handleEdgeNotStartsWith (Edge e) {
		/*if (!e.getSource().getSolution().startsWith(e.getDest().getSolution())) {
			//println (String.format("handleEdgeNotStartsWith return true ('%s'.notsw('%s'))", e.getSource().getSolution(), e.getDest().getSolution()));
			return true;
		}*/
		//println ("Entered handleEdgeNotStartsWith");
		
		//source.sw(dest)
		if (e.getSource().isConstant() && !e.getDest().isConstant()) {
			unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			Automaton destination = mapAutomaton.get(e.getDest());
			String source = e.getSource().getSolution();
			
			if (e.getDest().getLength() < e.getSource().getLength()) {
				String prefix = source.substring(0, e.getDest().getLength());
				destination = destination.minus(Automaton.makeString(prefix));
				if (destination.isEmpty()) {
					debug_unsat_reason = "Not handling of edge startswith, with source constant, lead to empty destination";
					return false;
				}
				
				e.getDest().setSolution(destination.getShortestExample(true));
				mapAutomaton.put(e.getDest(), destination);
			} else {
				destination = destination.minus(Automaton.makeString(source));
				if (destination.isEmpty()) {
					debug_unsat_reason = "Not handling of edge startswith, with source constant, lead to empty destination";
					return false;
				}
				
				e.getDest().setSolution(destination.getShortestExample(true));
				mapAutomaton.put(e.getDest(), destination);
			}
			
			
			global_change = true;
		} else if (!e.getSource().isConstant() && e.getDest().isConstant()) {
			unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			Automaton source = mapAutomaton.get(e.getSource());
			String destination = e.getDest().getSolution();
			
			Automaton temp = Automaton.makeString(destination).concatenate(AutomatonExtra.makeAnyStringFixed());
			source = source.minus(temp);
			if (source.isEmpty()) {
				debug_unsat_reason = "Not handling of edge startswith, with destination constant, lead to empty source";
				return false;
			}
			
			e.getSource().setSolution(source.getShortestExample(true));
			mapAutomaton.put(e.getSource(), source);
			global_change = true;
		} else if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			unsatStack1.add(excludeVertecis(e));
			notEdges.add(e);
		} else {
			//Everything is constant
			String source = e.getSource().getSolution();
			String dest = e.getDest().getSolution();
			return !source.startsWith(dest);
		}
		
		return true;
	}
	
	public static boolean handleEdgeNotEndsWith (Edge e) {
		//println ("handleEdgeNotEndsWith: " + e);
		//println ("e.getSource().isConstant() && e.getDest().isConstant(): " + e.getSource().isConstant() + " " + e.getDest().isConstant());
		/*if (!e.getSource().getSolution().endsWith(e.getDest().getSolution())) {
			//println ("return true");
			return true;
		}*/
		
		//source.sw(dest)
		if (e.getSource().isConstant() && !e.getDest().isConstant()) {
			//println ("e.getSource().isConstant() && !e.getDest().isConstant()");
			unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			Automaton destination = mapAutomaton.get(e.getDest());
			String source = e.getSource().getSolution();
			
			int diffLength = e.getSource().getLength() - e.getDest().getLength();
			
			if (diffLength >= 0) {
				String suffix = source.substring(diffLength);
				destination = destination.minus(Automaton.makeString(suffix));
				if (destination.isEmpty()) {
					debug_unsat_reason = "Not handling of edge endswith, with source constant, lead to empty destination";
					return false;
				}
				
				e.getDest().setSolution(destination.getShortestExample(true));
				mapAutomaton.put(e.getDest(), destination);
			} else {
				destination = destination.minus(Automaton.makeString(source));
				if (destination.isEmpty()) {
					debug_unsat_reason = "Not handling of edge endswith, with source constant, lead to empty destination";
					return false;
				}
				
				e.getDest().setSolution(destination.getShortestExample(true));
				mapAutomaton.put(e.getDest(), destination);
			}
			global_change = true;
		} else if (!e.getSource().isConstant() && e.getDest().isConstant()) {
			//println ("!e.getSource().isConstant() && e.getDest().isConstant()");
			unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			Automaton source = mapAutomaton.get(e.getSource());
			String destination = e.getDest().getSolution();
			
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination));
			source = source.minus(temp);
			if (source.isEmpty()) {
				debug_unsat_reason = "Not handling of edge endswith, with destination constant, lead to empty source";
				return false;
			}
			
			e.getSource().setSolution(source.getShortestExample(true));
			mapAutomaton.put(e.getSource(), source);
			global_change = true;
		} else if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			//println ("!e.getSource().isConstant() && !e.getDest().isConstant()");
			unsatStack1.add(excludeVertecis(e));
			notEdges.add(e);
		} else {
			//Everything is constant
			String source = e.getSource().getSolution();
			String dest = e.getDest().getSolution();
			return !source.endsWith(dest);
		}
		//println ("nothing");
		return true;
	}
	
	public static boolean handleEdgeNotContains (Edge e) {
		//println ("[handleEdgeNotContains] entered");
		/*if (!e.getSource().getSolution().contains(e.getDest().getSolution())) {
			return true;
		}*/
		
		//source.sw(dest)
		if (e.getSource().isConstant() && !e.getDest().isConstant()) {
			unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			Automaton destination = mapAutomaton.get(e.getDest());
			String source = e.getSource().getSolution();
			
			for (int i = 0; i <= e.getSource().getLength() - e.getDest().getLength(); i++) {
				String t = source.substring(i, i + e.getDest().getLength());
				destination = destination.minus(Automaton.makeString(t));
				if (destination.isEmpty()) {
					debug_unsat_reason = "Not handling of edge contains, with source constant, lead to empty destination";
					return false;
				}
			}
			
			e.getDest().setSolution(destination.getShortestExample(true));
			mapAutomaton.put(e.getDest(), destination);
			global_change = true;
		} else if (!e.getSource().isConstant() && e.getDest().isConstant()) {
			unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			Automaton source = mapAutomaton.get(e.getSource());
			String destination = e.getDest().getSolution();
			
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed());
			source = source.minus(temp);
			if (source.isEmpty()) {
				debug_unsat_reason = "Not handling of edge contains, with destination constant, lead to empty source";
				return false;
			}
			
			e.getSource().setSolution(source.getShortestExample(true));
			mapAutomaton.put(e.getSource(), source);
			global_change = true;
		} else if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			unsatStack1.add(excludeVertecis(e));
			notEdges.add(e);
		} else {
			//Everything is constant
			String source = e.getSource().getSolution();
			String dest = e.getDest().getSolution();
			return !source.contains(dest);
		}
		
		return true;
	}
	
	private static boolean handleNotEdgeIndexOf (EdgeIndexOf e) {
		/*if (e.getSource().getSolution().indexOf(e.getDest().getSolution()) == e.getIndex().solution()) {
			return true;
		}*/
		//println ("handleNotEdgeIndexOf entered");
		
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		if (e.getIndex().solution() < 0) {
			if (e.getSource().isConstant() && !e.getDest().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				Automaton destination = mapAutomaton.get(e.getDest());
				String source = e.getSource().getSolution();
				
				for (int i = 0; i <= e.getSource().getLength() - e.getDest().getLength(); i++) {
					String t = source.substring(i, i + e.getDest().getLength());
					destination = destination.minus(Automaton.makeString(t));
					if (destination.isEmpty()) {
						debug_unsat_reason = "Not handling of edge indexOf == -1, with source constant, lead to empty destination";
						return false;
					}
				}
				
				e.getDest().setSolution(destination.getShortestExample(true));
				mapAutomaton.put(e.getDest(), destination);
				global_change = true;
			} else if (!e.getSource().isConstant() && e.getDest().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = e.getDest().getSolution();
				
				Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed());
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			} else if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				unsatStack1.add(excludeVertecis(e));
				notEdges.add(e);
			} else {
				String source = e.getSource().getSolution();
				String dest = e.getDest().getSolution();
				return !source.contains(dest);
			}
		} else if (e.getIndex().solution() >= 0) {
			//So source before e.getIndex may not contain destination
			if (e.getSource().isConstant() && !e.getDest().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				Automaton destination = mapAutomaton.get(e.getDest());
				String source = e.getSource().getSolution();
				source = source.substring(0, e.getIndex().solutionInt()); //The part of source before e.getIndex()
				
				for (int i = 0; i <= source.length() - e.getDest().getLength(); i++) {
					String t = source.substring(i, i + e.getDest().getLength());
					destination = destination.minus(Automaton.makeString(t));
					if (destination.isEmpty()) {
						debug_unsat_reason = "Not handling of edge indexOf == -1, with source constant, lead to empty destination";
						return false;
					}
				}
				
				e.getDest().setSolution(destination.getShortestExample(true));
				mapAutomaton.put(e.getDest(), destination);
				global_change = true;
			} else if (!e.getSource().isConstant() && e.getDest().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = e.getDest().getSolution();
				
				Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed());
				temp = temp.intersection(AutomatonExtra.lengthAutomaton(e.getIndex().solutionInt()));
				temp = temp.concatenate(AutomatonExtra.makeAnyStringFixed());
				
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			} else if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				unsatStack1.add(excludeVertecis(e));
				notEdges.add(e);
			} else {
				String source = e.getSource().getSolution();
				String dest = e.getDest().getSolution();
				return source.indexOf(dest) == e.getIndex().solution();
			}
		}
		return true;
	}
	
	private static boolean handleNotEdgeIndexOfChar (EdgeIndexOfChar e) {
		/*if (e.getSource().getSolution().indexOf(e.getDest().getSolution()) == e.getIndex().solution()) {
			return true;
		}*/
		
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		if (e.getIndex().solution() < 0) {
			if (e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				
				for (int i = 0; i < e.getSource().getLength(); i++) {
					char c = e.getSource().getSolution().charAt(i);
					global_pc._addDet(Comparator.NE, new IntegerConstant(c), e.getIndex().getExpression());
				}
				
				//Check if everything is still solved:
				if (scg.isSatisfiable(global_pc)) {
					scg.solve(global_pc);
					global_pc.flagSolved = true;
					global_change = true;
					return true;
				} else {
					return false;
				}
				
			} else if (!e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = String.valueOf((char) e.getIndex().getExpression().solution());
				
				Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed());
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			}
		} else if (e.getIndex().solution() - 1 > 0) {
			//So source before e.getIndex may not contain destination
			if (e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				
				String source = e.getSource().getSolution();
				char destination = (char) e.getIndex().getExpression().solution();
				
				for (int i = 0; i < e.getIndex().solution(); i++) {
					char c = source.charAt(i);
					global_pc._addDet(Comparator.NE, new IntegerConstant(destination), new IntegerConstant(c));
				}
				
				//Check if everything is still solved:
				if (scg.isSatisfiable(global_pc)) {
					scg.solve(global_pc);
					global_pc.flagSolved = true;
					global_change = true;
					return true;
				} else {
					return false;
				}
			} else if (!e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = String.valueOf((char) e.getIndex().getExpression().solution());
				
				Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed());
				temp = temp.intersection(AutomatonExtra.lengthAutomaton(e.getIndex().solutionInt()));
				temp = temp.concatenate(AutomatonExtra.makeAnyStringFixed());
				
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			}
		}
		return true;
	}
	
	private static boolean handleNotEdgeLastIndexOfChar (EdgeLastIndexOfChar e) {
		/*if (e.getSource().getSolution().indexOf(e.getDest().getSolution()) == e.getIndex().solution()) {
			return true;
		}*/
		
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		if (e.getIndex().solution() < 0) { //Should not be contained anywhere
			//println ("[handleNotEdgeLastIndexOfChar] e.getIndex().solution() < 0");
			if (e.getSource().isConstant()) {
				//println ("[handleNotEdgeLastIndexOfChar] e.getSource().isConstant()");
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				
				for (int i = 0; i < e.getSource().getLength(); i++) {
					char c = e.getSource().getSolution().charAt(i);
					global_pc._addDet(Comparator.NE, new IntegerConstant(c), e.getIndex().getExpression());
				}
				
				//Check if everything is still solved:
				if (scg.isSatisfiable(global_pc)) {
					scg.solve(global_pc);
					global_pc.flagSolved = true;
					global_change = true;
					return true;
				} else {
					return false;
				}
				
			} else if (!e.getSource().isConstant()) {
				//println ("[handleNotEdgeLastIndexOfChar] !e.getSource().isConstant()"); 
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = String.valueOf((char) e.getIndex().getExpression().solution());
				
				Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed());
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			}
		} else if (e.getIndex().solution() >= 0) {
			//println ("[handleNotEdgeLastIndexOfChar] e.getIndex().solution() >= 0");
			//So source before e.getIndex may not contain destination
			if (e.getSource().isConstant()) {
				//println ("[handleNotEdgeLastIndexOfChar] e.getSource().isConstant()");
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				
				String source = e.getSource().getSolution();
				char destination = (char) e.getIndex().getExpression().solution();
				
				for (int i = e.getIndex().solutionInt() + 1; i < e.getSource().getLength(); i++) {
					char c = source.charAt(i);
					global_pc._addDet(Comparator.NE, new IntegerConstant(destination), new IntegerConstant(c));
				}
				
				//Check if everything is still solved:
				if (scg.isSatisfiable(global_pc)) {
					scg.solve(global_pc);
					global_pc.flagSolved = true;
					global_change = true;
					return true;
				} else {
					return false;
				}
			} else if (!e.getSource().isConstant()) {
				//println ("[handleNotEdgeLastIndexOfChar] !e.getSource().isConstant()");
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = String.valueOf((char) e.getIndex().getExpression().solution());
				
				Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed());
				temp = temp.intersection(AutomatonExtra.lengthAutomaton(e.getSource().getLength() - e.getIndex().solutionInt() -1));
				temp = AutomatonExtra.makeAnyStringFixed().concatenate(temp);
				//println ("[handleNotEdgeLastIndexOfChar] e.getSource().getLength(): " + e.getSource().getLength());
				//println ("[handleNotEdgeLastIndexOfChar] e.getIndex().solution(): " + e.getIndex().solution());
				//println ("[handleNotEdgeLastIndexOfChar] source example: '" + source.getShortestExample(true) + "'");
				//println ("[handleNotEdgeLastIndexOfChar] dest example: '" + destination + "'");
				//println ("[handleNotEdgeLastIndexOfChar] temp example: '" + temp.getShortestExample(true) + "'");
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge last indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			}
		}
		return true;
	}
	
	private static boolean handleNotEdgeIndexOfChar2 (EdgeIndexOfChar2 e) {
		/*if (e.getSource().getSolution().indexOf(e.getDest().getSolution()) == e.getIndex().solution()) {
			return true;
		}*/
		
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(e.getIndex().getMinDist().solution())));
		if (e.getIndex().solution() < 0) {
			if (e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				
				for (int i = e.getIndex().getMinDist().solutionInt(); i < e.getSource().getLength(); i++) {
					char c = e.getSource().getSolution().charAt(i);
					global_pc._addDet(Comparator.NE, new IntegerConstant(c), e.getIndex().getExpression());
				}
				
				//Check if everything is still solved:
				if (scg.isSatisfiable(global_pc)) {
					scg.solve(global_pc);
					global_pc.flagSolved = true;
					global_change = true;
					return true;
				} else {
					return false;
				}
			} else if (!e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = String.valueOf((char) e.getIndex().getExpression().solution());
				
				Automaton temp = AutomatonExtra.lengthAutomaton(e.getIndex().getMinDist().solutionInt()).concatenate(AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed()));
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			}
		} else if (e.getIndex().solution() - 1 - e.getIndex().getMinDist().solution() > 0) {
			//So source before e.getIndex may not contain destination
			if (e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				
				String source = e.getSource().getSolution();
				char destination = (char) e.getIndex().getExpression().solution();
				
				for (int i = e.getIndex().getMinDist().solutionInt(); i < e.getIndex().solution(); i++) {
					char c = source.charAt(i);
					global_pc._addDet(Comparator.NE, new IntegerConstant(destination), new IntegerConstant(c));
				}
				
				//Check if everything is still solved:
				if (scg.isSatisfiable(global_pc)) {
					scg.solve(global_pc);
					global_pc.flagSolved = true;
					global_change = true;
					return true;
				} else {
					return false;
				}
			} else if (!e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = String.valueOf((char) e.getIndex().getExpression().solution());
				
				Automaton temp = AutomatonExtra.lengthAutomaton(e.getIndex().getMinDist().solutionInt()).concatenate(AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed()));
				temp = temp.intersection(AutomatonExtra.lengthAutomaton(e.getIndex().solutionInt()));
				temp = temp.concatenate(AutomatonExtra.makeAnyStringFixed());
				
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			}
		}
		return true;
	}
	
	private static boolean handleNotEdgeLastIndexOfChar2 (EdgeLastIndexOfChar2 e) {
		/*if (e.getSource().getSolution().indexOf(e.getDest().getSolution()) == e.getIndex().solution()) {
			return true;
		}*/
		
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex().getExpression(), Comparator.NE, new IntegerConstant(e.getIndex().getExpression().solution())));
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(e.getIndex().getMinDist().solution())));
		if (e.getIndex().solution() < 0) {
			if (e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				
				for (int i = e.getIndex().getMinDist().solutionInt(); i < e.getSource().getLength(); i++) {
					char c = e.getSource().getSolution().charAt(i);
					global_pc._addDet(Comparator.NE, new IntegerConstant(c), e.getIndex().getExpression());
				}
				
				//Check if everything is still solved:
				if (scg.isSatisfiable(global_pc)) {
					scg.solve(global_pc);
					global_pc.flagSolved = true;
					global_change = true;
					return true;
				} else {
					return false;
				}
			} else if (!e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = String.valueOf((char) e.getIndex().getExpression().solution());
				
				Automaton temp = AutomatonExtra.lengthAutomaton(e.getIndex().getMinDist().solutionInt()).concatenate(AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed()));
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			}
		} else if (e.getIndex().solution() - 1 - e.getIndex().getMinDist().solution() > 0) {
			//So source before e.getIndex may not contain destination
			if (e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				
				String source = e.getSource().getSolution();
				char destination = (char) e.getIndex().getExpression().solution();
				
				for (int i = e.getIndex().getMinDist().solutionInt(); i < e.getSource().getLength(); i++) {
					char c = source.charAt(i);
					global_pc._addDet(Comparator.NE, new IntegerConstant(destination), new IntegerConstant(c));
				}
				
				//Check if everything is still solved:
				if (scg.isSatisfiable(global_pc)) {
					scg.solve(global_pc);
					global_pc.flagSolved = true;
					global_change = true;
					return true;
				} else {
					return false;
				}
			} else if (!e.getSource().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = String.valueOf((char) e.getIndex().getExpression().solution());
				
				Automaton temp = AutomatonExtra.lengthAutomaton(e.getIndex().getMinDist().solutionInt()).concatenate(AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed()));
				temp = temp.intersection(AutomatonExtra.lengthAutomaton(e.getSource().getLength() - e.getIndex().solutionInt() - 1));
				temp = AutomatonExtra.makeAnyStringFixed().concatenate(temp);
				
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			}
		}
		return true;
	}
	
	private static boolean handleNotEdgeIndexOf2 (EdgeIndexOf2 e) {
		/*if (e.getSource().getSolution().indexOf(e.getDest().getSolution(), e.getIndex().getMinIndex().solution()) == e.getIndex().solution()) {
			return true;
		}*/
		
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
		unsatStack2.add(new LinearIntegerConstraint(e.getIndex().getMinIndex(), Comparator.NE, new IntegerConstant(e.getIndex().getMinIndex().solution())));
		if (e.getIndex().solution() < 0) {
			if (e.getSource().isConstant() && !e.getDest().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				Automaton destination = mapAutomaton.get(e.getDest());
				String source = e.getSource().getSolution();
				
				for (int i = e.getIndex().getMinIndex().solutionInt(); i <= e.getSource().getLength() - e.getDest().getLength(); i++) {
					String t = source.substring(i, i + e.getDest().getLength());
					destination = destination.minus(Automaton.makeString(t));
					if (destination.isEmpty()) {
						debug_unsat_reason = "Not handling of edge indexOf == -1, with source constant, lead to empty destination";
						return false;
					}
				}
				
				e.getDest().setSolution(destination.getShortestExample(true));
				mapAutomaton.put(e.getDest(), destination);
				global_change = true;
			} else if (!e.getSource().isConstant() && e.getDest().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = e.getDest().getSolution();
				
				Automaton temp = AutomatonExtra.lengthAutomaton(e.getIndex().getMinIndex().solutionInt()).concatenate(AutomatonExtra.makeAnyStringFixed()).concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed());
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			} else if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				unsatStack1.add(excludeVertecis(e));
				notEdges.add(e);
			} else {
				throw new RuntimeException("This should not be reached");
			}
		} else if (e.getIndex().solution() - e.getDest().getLength() - e.getIndex().getMinIndex().solution() > 0) {
			//So source before e.getIndex may not contain destination
			if (e.getSource().isConstant() && !e.getDest().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
				Automaton destination = mapAutomaton.get(e.getDest());
				String source = e.getSource().getSolution();
				source = source.substring(e.getIndex().getMinIndex().solutionInt(), e.getIndex().solutionInt()); //The part of source before e.getIndex()
				
				for (int i = e.getIndex().getMinIndex().solutionInt(); i <= source.length() - e.getDest().getLength(); i++) {
					String t = source.substring(i, i + e.getDest().getLength());
					destination = destination.minus(Automaton.makeString(t));
					if (destination.isEmpty()) {
						debug_unsat_reason = "Not handling of edge indexOf == -1, with source constant, lead to empty destination";
						return false;
					}
				}
				
				e.getDest().setSolution(destination.getShortestExample(true));
				mapAutomaton.put(e.getDest(), destination);
				global_change = true;
			} else if (!e.getSource().isConstant() && e.getDest().isConstant()) {
				unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
				Automaton source = mapAutomaton.get(e.getSource());
				String destination = e.getDest().getSolution();
				
				Automaton temp = AutomatonExtra.lengthAutomaton(e.getIndex().getMinIndex().solutionInt()).concatenate(AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(destination)).concatenate(AutomatonExtra.makeAnyStringFixed()));
				temp = temp.intersection(AutomatonExtra.lengthAutomaton(e.getIndex().solutionInt()));
				temp = temp.concatenate(AutomatonExtra.makeAnyStringFixed());
				
				source = source.minus(temp);
				if (source.isEmpty()) {
					debug_unsat_reason = "Not handling of edge indexOf == -1, with destination constant, lead to empty source";
					return false;
				}
				
				e.getSource().setSolution(source.getShortestExample(true));
				mapAutomaton.put(e.getSource(), source);
				global_change = true;
			} else if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				unsatStack1.add(excludeVertecis(e));
				
				notEdges.add(e);
			} else {
				throw new RuntimeException("This should not be reached");
			}
		}
		return true;
	}
	
	/* NOT HANDLING END */
	
	/* ITERATING THROUGH POSSIBILITIES START */
	
	private static boolean handleVarVarNots () {
		if (notEdges.size() == 0) {
			return true;
		}
		
		//Setup base
		int base = 0;
		//println ("notEdges: " + notEdges);
		for (Edge e: notEdges) {
			Vertex source = e.getSource();
			Vertex dest = e.getDest();
			if (mapVertexInteger.get(source) == null) {
				mapVertexInteger.put(source, base);
				base++;
			}
			if (mapVertexInteger.get(dest) == null) {
				mapVertexInteger.put(dest, base);
				base++;
			}
		}
		//base--;
		//println ("mapVertexInteger: " + mapVertexInteger);
		//println ("base: " + base);
		
		//Setup solutions
		for (Edge e: notEdges) {
			if (e instanceof EdgeNotEqual) {
				handleEdgeNotEqualVarVar((EdgeNotEqual) e, base);
			} else if (e instanceof EdgeNotStartsWith) {
				handleEdgeNotStartsWithVarVar((EdgeNotStartsWith) e, base);
			} else if (e instanceof EdgeNotEndsWith) {
				handleEdgeNotEndsWithVarVar((EdgeNotEndsWith) e, base);
			} else if (e instanceof EdgeNotContains) {
				handleEdgeNotContainsVarVar((EdgeNotContains) e, base);
			} else if (e instanceof EdgeIndexOf) {
				handleEdgeIndexOfVarVar((EdgeIndexOf) e, base);
			} else if (e instanceof EdgeIndexOf2) {
				handleEdgeIndexOf2VarVar((EdgeIndexOf2) e, base);
			/*} else if (e instanceof EdgeIndexOfChar) { Not neccassery
				handleEdgeIndexOfCharVarVar((EdgeIndexOfChar) e, base);
			} else if (e instanceof EdgeIndexOfChar2) {
				handleEdgeIndexOfChar2VarVar((EdgeIndexOfChar2) e, base); */
			} else {
				throw new RuntimeException("Unsupported not edge encountered");
			}
		}
		
		//Setup iteration
		List<Integer> iteration = new ArrayList<Integer>(base);
		for (int i = 0; i < base; i++) {
			iteration.add(new Integer(0));
		}
		
		//Run through iterations
		boolean result = false;
		boolean overflow = false;
		while (result == false && overflow == false) {
			//println ("iteration: " + iteration);
			result = run(iteration, base);
			if (result == true) {break;}
			overflow = increment(iteration, base);
		}
		
		if (overflow == true) {
			//println ("overflow");
			return false;
		}
		
		for (Entry<Vertex, Integer> e: mapVertexInteger.entrySet()) {
			int index = e.getValue();
			Vertex v = e.getKey();
			v.setSolution(concreteMap.get(v).get(iteration.get(index)));
		}
		
		return result;
	}
	
	private static void handleEdgeNotEqualVarVar (EdgeNotEqual e, int base) {
		if (e.getDest().isConstant() || e.getSource().isConstant()) {
			throw new RuntimeException("Assumption fail");
		}
		
		Automaton s = mapAutomaton.get(e.getSource());
		//println ("[handleEdgeNotEqualVarVar] base: " + base);
		String[] sourceSolutions = new String[base];
		for (int i = 0; i < base; i++) {
			String solution = s.getShortestExample(true);
			sourceSolutions[i] = solution;
			s = s.minus(Automaton.makeString(solution));
		}
		
		Automaton d = mapAutomaton.get(e.getDest());
		String[] destSolutions = new String[base];
		for (int i = 0; i < base; i++) {
			String solution = d.getShortestExample(true);
			destSolutions[i] = solution;
			d = d.minus(Automaton.makeString(solution));
		}
		
		concreteMap.put(e.getSource(), convertToList(sourceSolutions));
		concreteMap.put(e.getDest(), convertToList(destSolutions));
	}
	
	private static List<String> convertToList (String[] arg) {
		List<String> result = new ArrayList<String>(arg.length);
		for (String s: arg) {
			result.add(s);
		}
		return result;
	}
	
	private static void handleEdgeNotStartsWithVarVar (EdgeNotStartsWith e, int base) {
		if (e.getDest().isConstant() || e.getSource().isConstant()) {
			throw new RuntimeException("Assumption fail");
		}
		
		Automaton s = mapAutomaton.get(e.getSource());
		//println ("[handleEdgeNotStartsWithVarVar] base: " + base);
		String[] sourceSolutions = new String[base];
		for (int i = 0; i < base; i++) {
			String solution = s.getShortestExample(true);
			sourceSolutions[i] = solution;
			s = s.minus(Automaton.makeString(solution));
		}
		
		Automaton d = mapAutomaton.get(e.getDest());
		String[] destSolutions = new String[base];
		for (int i = 0; i < base; i++) {
			String solution = d.getShortestExample(true);
			destSolutions[i] = solution;
			d = d.minus(Automaton.makeString(solution));
		}
		
		concreteMap.put(e.getSource(), convertToList(sourceSolutions));
		concreteMap.put(e.getDest(), convertToList(destSolutions));
	}
	
	private static void handleEdgeNotEndsWithVarVar (EdgeNotEndsWith e, int base) {
		if (e.getDest().isConstant() || e.getSource().isConstant()) {
			throw new RuntimeException("Assumption fail");
		}
		
		Automaton s = mapAutomaton.get(e.getSource());
		//println ("[handleEdgeNotEndsWithVarVar] base: " + base);
		String[] sourceSolutions = new String[base];
		for (int i = 0; i < base; i++) {
			String solution = s.getShortestExample(true);
			sourceSolutions[i] = solution;
			s = s.minus(Automaton.makeString(solution));
		}
		
		Automaton d = mapAutomaton.get(e.getDest());
		String[] destSolutions = new String[base];
		for (int i = 0; i < base; i++) {
			String solution = d.getShortestExample(true);
			destSolutions[i] = solution;
			d = d.minus(Automaton.makeString(solution));
		}
		
		concreteMap.put(e.getSource(), convertToList(sourceSolutions));
		concreteMap.put(e.getDest(), convertToList(destSolutions));
	}
	
	private static void handleEdgeNotContainsVarVar (EdgeNotContains e, int base) {
		if (e.getDest().isConstant() || e.getSource().isConstant()) {
			throw new RuntimeException("Assumption fail");
		}
		
		Automaton s = mapAutomaton.get(e.getSource());
		//println ("[handleEdgeNotContainsVarVar] base: " + base);
		String[] sourceSolutions = new String[base];
		for (int i = 0; i < base; i++) {
			String solution = s.getShortestExample(true);
			sourceSolutions[i] = solution;
			s = s.minus(Automaton.makeString(solution));
		}
		
		Automaton d = mapAutomaton.get(e.getDest());
		String[] destSolutions = new String[base];
		for (int i = 0; i < base; i++) {
			String solution = d.getShortestExample(true);
			destSolutions[i] = solution;
			d = d.minus(Automaton.makeString(solution));
		}
		
		concreteMap.put(e.getSource(), convertToList(sourceSolutions));
		concreteMap.put(e.getDest(), convertToList(destSolutions));
	}
	
	private static void handleEdgeIndexOfVarVar (EdgeIndexOf e, int base) {
		if (e.getDest().isConstant() || e.getSource().isConstant()) {
			throw new RuntimeException("Assumption fail");
		}
		//println ("e.getIndex().solution(): " + e.getIndex().solution());
		if (e.getIndex().solution() < 0) {
			Automaton s = mapAutomaton.get(e.getSource());
			//println ("[handleEdgeNotIndexOfVarVar] base: " + base);
			String[] sourceSolutions = new String[base];
			for (int i = 0; i < base; i++) {
				String solution = s.getShortestExample(true);
				sourceSolutions[i] = solution;
				s = s.minus(Automaton.makeString(solution));
			}
			
			Automaton d = mapAutomaton.get(e.getDest());
			String[] destSolutions = new String[base];
			for (int i = 0; i < base; i++) {
				String solution = d.getShortestExample(true);
				destSolutions[i] = solution;
				d = d.minus(Automaton.makeString(solution));
			}
			
			concreteMap.put(e.getSource(), convertToList(sourceSolutions));
			concreteMap.put(e.getDest(), convertToList(destSolutions));
		} else if (e.getIndex().solution() >= 0) {
			Automaton source = mapAutomaton.get(e.getSource());
			Automaton dest = mapAutomaton.get(e.getDest());
			
			int index = e.getIndex().solutionInt();
			//println ("index: " + index);
			String[] sourceSolutions = new String[base];
			String[] destSolutions = new String[base];
			
			int count = 0;
			while (count < base) {
				String destConc = dest.getShortestExample(true);
				Automaton prefix = AutomatonExtra.lengthAutomaton(index);
				Automaton temp = prefix.concatenate(Automaton.makeString(destConc)).concatenate(AutomatonExtra.makeAnyStringFixed());
				Automaton intersection = source.intersection(temp);
				if (!intersection.isEmpty()) {
					destSolutions[count] = destConc;
					String tempSource = intersection.getShortestExample(true);
					sourceSolutions[count] = tempSource;
					dest = dest.minus(Automaton.makeString(destConc));
					source = source.minus(Automaton.makeString(tempSource));
					//println (String.format("'%s'.indexOf('%s') == %d", tempSource, destConc, tempSource.indexOf(destConc)));
					if (tempSource.indexOf(destConc) == index) {
						count++;
					}
				} else {
					dest = dest.minus(Automaton.makeString(destConc)); 
					if (dest.isEmpty()) {
						debug_unsat_reason = "Could not figure out indexOf";
						//throw new RuntimeException("Condition not handled just yet");
						destSolutions[count] = destSolutions[count-1];
						sourceSolutions[count] = sourceSolutions[count-1];
						count++;
					}
				}
			}
			//println ("Source: " + convertToList(sourceSolutions));
			//println ("Dest: " + convertToList(destSolutions));
			concreteMap.put(e.getSource(), convertToList(sourceSolutions));
			concreteMap.put(e.getDest(), convertToList(destSolutions));
		}
	}
	
	private static void handleEdgeIndexOf2VarVar (EdgeIndexOf2 e, int base) {
		if (e.getDest().isConstant() || e.getSource().isConstant()) {
			throw new RuntimeException("Assumption fail");
		}
		
		if (e.getIndex().solution() < 0) {
			Automaton s = mapAutomaton.get(e.getSource());
			//println ("[handleEdgeNotIndexOf2VarVar] base: " + base);
			String[] sourceSolutions = new String[base];
			for (int i = 0; i < base; i++) {
				String solution = s.getShortestExample(true);
				sourceSolutions[i] = solution;
				s = s.minus(Automaton.makeString(solution));
			}
			
			Automaton d = mapAutomaton.get(e.getDest());
			String[] destSolutions = new String[base];
			for (int i = 0; i < base; i++) {
				String solution = d.getShortestExample(true);
				destSolutions[i] = solution;
				d = d.minus(Automaton.makeString(solution));
			}
			
			concreteMap.put(e.getSource(), convertToList(sourceSolutions));
			concreteMap.put(e.getDest(), convertToList(destSolutions));
		} else if (e.getIndex().solution() >= 0) {
			Automaton source = mapAutomaton.get(e.getSource());
			Automaton dest = mapAutomaton.get(e.getDest());
			
			int index = e.getIndex().solutionInt();
			int minIndex = e.getIndex().getMinIndex().solutionInt();
			//println ("index: " + index);
			String[] sourceSolutions = new String[base];
			String[] destSolutions = new String[base];
			
			int count = 0;
			while (count < base) {
				String destConc = dest.getShortestExample(true);
				Automaton prefix = AutomatonExtra.lengthAutomaton(index);
				Automaton temp = prefix.concatenate(Automaton.makeString(destConc)).concatenate(AutomatonExtra.makeAnyStringFixed());
				Automaton intersection = source.intersection(temp);
				if (!intersection.isEmpty()) {
					destSolutions[count] = destConc;
					String tempSource = intersection.getShortestExample(true);
					sourceSolutions[count] = tempSource;
					dest = dest.minus(Automaton.makeString(destConc));
					source = source.minus(Automaton.makeString(tempSource));
					//println (String.format("'%s'.indexOf('%s') == %d", tempSource, destConc, tempSource.indexOf(destConc)));
					if (tempSource.indexOf(destConc, minIndex) == index) {
						count++;
					}
				} else {
					dest = dest.minus(Automaton.makeString(destConc)); 
					if (dest.isEmpty()) {
						debug_unsat_reason = "Could not figure out indexOf";
						//throw new RuntimeException("Condition not handled just yet");
						destSolutions[count] = destSolutions[count-1];
						sourceSolutions[count] = sourceSolutions[count-1];
						count++;
					}
				}
			}
			//println ("Source: " + convertToList(sourceSolutions));
			//println ("Dest: " + convertToList(destSolutions));
			concreteMap.put(e.getSource(), convertToList(sourceSolutions));
			concreteMap.put(e.getDest(), convertToList(destSolutions));

		}
	}

	
	private static boolean run(List<Integer> iteration, int base) {
		for (Edge e: notEdges) {
			boolean result = true;
			if (e instanceof EdgeNotEqual) {
				result = handleEdgeNotEqual((EdgeNotEqual) e, iteration, base);
			} else if (e instanceof EdgeNotStartsWith) {
				result = handleEdgeNotStartsWith((EdgeNotStartsWith) e, iteration, base);
			}
			else if (e instanceof EdgeNotEndsWith) {
				result = handleEdgeNotEndsWith((EdgeNotEndsWith) e, iteration, base);
			}
			else if (e instanceof EdgeNotContains) {
				result = handleEdgeNotContains((EdgeNotContains) e, iteration, base);
			}
			else if (e instanceof EdgeIndexOf) {
				result = handleEdgeIndexOf((EdgeIndexOf) e, iteration, base);
			}
			else if (e instanceof EdgeIndexOf2) {
				result = handleEdgeIndexOf2((EdgeIndexOf2) e, iteration, base);
			}
			else if (e instanceof EdgeIndexOfChar) {
				result = handleEdgeIndexOfChar((EdgeIndexOfChar) e, iteration, base);
			}
			else if (e instanceof EdgeIndexOfChar2) {
				result = handleEdgeIndexOfChar2((EdgeIndexOfChar2) e, iteration, base);
			}
			else if (e instanceof EdgeLastIndexOfChar) {
				result = handleEdgeLastIndexOfChar((EdgeLastIndexOfChar) e, iteration, base);
			}
			else if (e instanceof EdgeLastIndexOfChar2) {
				result = handleEdgeLastIndexOfChar2((EdgeLastIndexOfChar2) e, iteration, base);
			}
			if (result == false) {
				return result;
			}
		}
		return true;
	}
	
	private static boolean handleEdgeNotEqual (EdgeNotEqual e, List<Integer> iteration, int base) {
		int sourceNum = mapVertexInteger.get(e.getSource());
		int destNum = mapVertexInteger.get(e.getDest());
		
		String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
		String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
		
		if (source == null) {
			unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			return false;
		}
		
		if (dest == null) {
			unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			return false;
		}
		
		return !source.equals(dest);
	}
	
	private static boolean handleEdgeNotStartsWith (EdgeNotStartsWith e, List<Integer> iteration, int base) {
		int sourceNum = mapVertexInteger.get(e.getSource());
		int destNum = mapVertexInteger.get(e.getDest());
		
		String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
		String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
	
		if (source == null) {
			unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			return false;
		}
		
		if (dest == null) {
			unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			return false;
		}
		
		return !source.startsWith(dest);
	}
	
	private static boolean handleEdgeNotEndsWith (EdgeNotEndsWith e, List<Integer> iteration, int base) {
		int sourceNum = mapVertexInteger.get(e.getSource());
		int destNum = mapVertexInteger.get(e.getDest());
		
		String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
		String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
		
		if (source == null) {
			unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			return false;
		}
		
		if (dest == null) {
			unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			return false;
		}
		
		return !source.endsWith(dest);
	}
	
	private static boolean handleEdgeNotContains (EdgeNotContains e, List<Integer> iteration, int base) {
		//println ("[handleEdgeNotContains] entered");
		int sourceNum = mapVertexInteger.get(e.getSource());
		int destNum = mapVertexInteger.get(e.getDest());
		
		String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
		String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
		
		if (source == null) {
			unsatStack2.add(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			return false;
		}
		
		if (dest == null) {
			unsatStack2.add(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			return false;
		}
		
		return !source.contains(dest);
	}
	
	private static boolean handleEdgeIndexOf (EdgeIndexOf e, List<Integer> iteration, int base) {
		if (e.getIndex().solution() < 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return !source.contains(dest);
		} else if (e.getIndex().solution() >= 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			//println (String.format("%s.indexOf(%s) == %d (%d)", source, dest, e.getIndex().solution(), source.indexOf(dest)));
			return source.indexOf(dest) == e.getIndex().solution();
		}
		throw new RuntimeException("This should not be reached");
	}
	
	private static boolean handleEdgeIndexOf2 (EdgeIndexOf2 e, List<Integer> iteration, int base) {
		if (e.getIndex().solution() < 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.indexOf(dest, e.getIndex().getMinIndex().solutionInt()) == -1;
		} else if (e.getIndex().solution() >= 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.indexOf(dest, e.getIndex().getMinIndex().solutionInt()) == e.getIndex().solution();
		}
		throw new RuntimeException("This should not be reached");
	}
	
	private static boolean handleEdgeIndexOfChar (EdgeIndexOfChar e, List<Integer> iteration, int base) {
		if (e.getIndex().solution() < 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.indexOf(dest) == -1;
		} else if (e.getIndex().solution() >= 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.indexOf(dest) == e.getIndex().solution();
		}
		throw new RuntimeException("This should not be reached");
	}
	
	private static boolean handleEdgeLastIndexOfChar (EdgeLastIndexOfChar e, List<Integer> iteration, int base) {
		if (e.getIndex().solution() < 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.lastIndexOf(dest) == -1;
		} else if (e.getIndex().solution() >= 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.lastIndexOf(dest) == e.getIndex().solution();
		}
		throw new RuntimeException("This should not be reached");
	}
	
	private static boolean handleEdgeLastIndexOfChar2 (EdgeLastIndexOfChar2 e, List<Integer> iteration, int base) {
		if (e.getIndex().solution() < 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.lastIndexOf(dest, e.getIndex().getMinDist().solutionInt()) == -1;
		} else if (e.getIndex().solution() >= 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.lastIndexOf(dest, e.getIndex().getMinDist().solutionInt()) == e.getIndex().solution();
		}
		throw new RuntimeException("This should not be reached");
	}
	
	private static boolean handleEdgeIndexOfChar2 (EdgeIndexOfChar2 e, List<Integer> iteration, int base) {
		if (e.getIndex().solution() < 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.indexOf(dest, e.getIndex().getMinDist().solutionInt()) == -1;
		} else if (e.getIndex().solution()  >= 0) {
			int sourceNum = mapVertexInteger.get(e.getSource());
			int destNum = mapVertexInteger.get(e.getDest());
			
			String source = concreteMap.get(e.getSource()).get(iteration.get(sourceNum));
			String dest = concreteMap.get(e.getDest()).get(iteration.get(destNum));
			
			return source.indexOf(dest, e.getIndex().getMinDist().solutionInt()) == e.getIndex().solution();
		}
		throw new RuntimeException("This should not be reached");
	}
	
	private static boolean increment (List<Integer> number, int base) {
		boolean overflow = false;
		for (int i = number.size() - 1; i >= 0; i--) {
			int num = number.get(i);
			num = num + 1;
			if (num == base) {
				if (i == 0) {
					return true; 
				}
				number.set(i, 0);
			} else {
				number.set(i, num);
				break;
			}
		}
		return overflow;
	}
	
	/* ITERATING THROUGH POSSIBILITIES END */
	
	private static LogicalORLinearIntegerConstraints excludeVertecis(Edge e) {
		if (e instanceof EdgeConcat) {
			LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getSources().get(0).getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSources().get(0).getLength())));
			loic.addToList(new LinearIntegerConstraint(e.getSources().get(1).getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSources().get(1).getLength())));
			loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			return loic;
		} else {
			LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getSource().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getSource().getLength())));
			loic.addToList(new LinearIntegerConstraint(e.getDest().getSymbolicLength(), Comparator.NE, new IntegerConstant(e.getDest().getLength())));
			return loic;
		}
	}
	
}

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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import choco.Constraint;

import dk.brics.automaton.Automaton;
import dk.brics.string.stringoperations.Replace1;
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
import gov.nasa.jpf.symbc.string.graph.EdgeLastIndexOf;
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
import gov.nasa.jpf.util.LogManager;
import java.util.logging.Logger;

public class TranslateToAutomata {
  static Logger logger = LogManager.getLogger("TranslateToAutomata");

	private static Map<Vertex, Integer> mapSolved;
	private static Map<Vertex, Automaton> mapAutomaton;
	private static Map<Vertex, Integer> mapEdgeCount;
	private static Map<EdgeConcat, Integer> mapConcat;
	
	private static StringGraph global_graph;
	private static PathCondition global_pc;
	private static Map<List<gov.nasa.jpf.symbc.numeric.Constraint>, Map<Vertex, Automaton>> memo;
	private static int concatCount = 128;
	
	static SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
	
	public static long duration = 0;
	public static long int_duration = 0;
	public static long loops = 0;
	
	public static boolean isSat (StringGraph g, PathCondition pc) {
		long starttime = System.currentTimeMillis();
		boolean result = inner_isSat(g, pc);
		duration = duration + (System.currentTimeMillis() - starttime);
		return result;
	}
	
	/*
	 * The trim operation from JSA does not work with length of 1 characters!!
	 */
	private static boolean inner_isSat (StringGraph g, PathCondition pc) {
		/*mapAutomaton = null;
		if (memo == null) {
			memo = new HashMap<List<gov.nasa.jpf.symbc.numeric.Constraint>, Map<Vertex,Automaton>>();
		}
		List<gov.nasa.jpf.symbc.numeric.Constraint> listOfConstraints = new ArrayList<gov.nasa.jpf.symbc.numeric.Constraint>();
		if (pc.header != null) {
			gov.nasa.jpf.symbc.numeric.Constraint constraint = pc.header.and;
			while (constraint != null) {
				listOfConstraints.add(constraint);
				constraint = constraint.and;
			}
			Map<Vertex, Automaton> tempMemo = memo.get(listOfConstraints);
			if (tempMemo != null) {
				//println ("[isSat] remembered");
				mapAutomaton = new HashMap<Vertex, Automaton>(tempMemo);
			}
		}*/
		mapAutomaton = null;
		//println ("[isSat] integer constraints: " + pc.header);
		boolean restart = true;
		while (restart) {
			//println ("[isSat] restart");
			/* check if there was a timeout */
			SymbolicStringConstraintsGeneral.checkTimeOut();
			
			restart = false;
			global_graph = g;
			global_pc  = pc;
			mapSolved = new HashMap<Vertex, Integer>();
			
			mapConcat = new HashMap<EdgeConcat, Integer>();
			
			
			//Find the leaves (all vertecis with only one edge)
			mapEdgeCount = new HashMap<Vertex, Integer>();
			for (Edge e: g.getEdges()) {
				if (e instanceof EdgeConcat) {
					Integer i = mapEdgeCount.get(e.getSources().get(0));
					if (i == null) {
						mapEdgeCount.put(e.getSources().get(0), new Integer(1));
					}
					else {
						mapEdgeCount.put(e.getSources().get(0), new Integer(i+1));
					}
					i = mapEdgeCount.get(e.getSources().get(1));
					if (i == null) {
						mapEdgeCount.put(e.getSources().get(1), new Integer(1));
					}
					else {
						mapEdgeCount.put(e.getSources().get(1), new Integer(i+1));
					}
					i = mapEdgeCount.get(e.getDest());
					if (i == null) {
						mapEdgeCount.put(e.getDest(), new Integer(1));
					}
					else {
						mapEdgeCount.put(e.getDest(), new Integer(i+1));
					}
				}
				else {
					Integer i = mapEdgeCount.get(e.getSource());
					if (i == null) {
						mapEdgeCount.put(e.getSource(), new Integer(1));
					}
					else {
						mapEdgeCount.put(e.getSource(), new Integer(i+1));
					}
					i = mapEdgeCount.get(e.getDest());
					if (i == null) {
						mapEdgeCount.put(e.getDest(), new Integer(1));
					}
					else {
						mapEdgeCount.put(e.getDest(), new Integer(i+1));
					}
				}
			}
			for (Vertex v: g.getVertices()) {
				if (mapEdgeCount.get(v) == null) {
					mapEdgeCount.put(v, new Integer (0));
				}
			}
			int max = 0;
			for (Entry<Vertex, Integer> e: mapEdgeCount.entrySet()) {
				if (e.getValue() > max) {
					max = e.getValue();
				}
			}
			
			//Take the leaves, and intersect with sources
			boolean result = false;
			while (!result && g.getEdges().size() > 0) {
				/* check if there was a timeout */
				SymbolicStringConstraintsGeneral.checkTimeOut();
				//if (mapAutomaton == null) {
					mapAutomaton = new HashMap<Vertex, Automaton>();
					for (Vertex v: g.getVertices()) {
						mapSolved.put(v, new Integer(0));						
						Automaton length = AutomatonExtra.lengthAutomaton(v.getLength());
						Automaton toput;
						if (!v.isConstant()) {
							toput = AutomatonExtra.makeAnyStringFixed().intersection(length);
							//mapAutomaton.put(v, );
						}
						else {
							toput = Automaton.makeString(v.getSolution()).intersection(length);
							//mapAutomaton.put(v, );
						}
						//println ("[isSat] resetting " + v.getName() + " to '" + toput.getShortestExample(true) + "'");
						mapAutomaton.put(v, toput);
						if (!v.isConstant()) v.setSolution(toput.getShortestExample(true));
					}
					
				//}
				/*for (Vertex v: g.getVertices()) {
					//println ("here");
					mapSolved.put(v, new Integer(0));
					Automaton length = AutomatonExtra.lengthAutomaton(v.getLength());
					Automaton toput;
					if (!v.isConstant()) {
						toput = AutomatonExtra.makeAnyStringFixed().intersection(length);
						//mapAutomaton.put(v, );
					}
					else {
						toput = Automaton.makeString(v.getSolution()).intersection(length);
						//mapAutomaton.put(v, );
					}
					//println ("[isSat] resetting " + v.getName() + " to '" + toput.getShortestExample(true) + "'");
					mapAutomaton.put(v, toput);
					if (!v.isConstant()) v.setSolution(toput.getShortestExample(true));
				}*/
				
				result = true;
				//println ("[isSat] mapEdgeCount: " + mapEdgeCount);
				//println ("[isSat] max: " + max);
				for (int i = 0; i <= max; i++) {
					for (Vertex v: g.getVertices()) {
						
						if (mapEdgeCount.get(v) != i) continue;
						//println ("[isSat] Looking at: " + v.getName());
						//Find all the edges it features in (there is only one)
						//Vertex otherVertex;
						List<Edge> edges = new ArrayList<Edge>();
						for (Edge e: g.getEdges()) {
							if (e instanceof EdgeConcat) {
								if (e.getDest().equals(v) ||
									e.getSources().get(0).equals(v) ||
									e.getSources().get(1).equals(v)) {
									if (!edges.contains(e)) edges.add(e);
								}
							}
							else {
								if (e.getDest().equals(v) || e.getSource().equals(v)) {
									if (!edges.contains(e)) edges.add(e);
								}
							}
						}
						for (Edge edge: edges) {
							result = handle (edge);
							if (!result) {
								//Check if path condition has changed
								if (PathCondition.flagSolved == false) {
									loops++;
									logger.info ("[isSat] solving path condition: ");
									logger.info(global_pc.header.toString());
									long startTime = System.currentTimeMillis();
									boolean temp_result = scg.isSatisfiable(global_pc);
									long temp_dur = System.currentTimeMillis() - startTime;
									int_duration += temp_dur;
									duration -= temp_dur;
									if (temp_result) {
										scg.solve(global_pc);
										//println ("[isSat] solved");
										PathCondition.flagSolved = true;
										//println(global_pc.header.toString());
										restart = true;
										result = false;
										break;
									}
									else {
										//println ("[isSat] path condition could not be solved");
										return false;
									}
								}
								else {
									//println ("Path condition did not change");
									return false;
								}
							}
						}
						if (result == false) break;
					}
					if (result == false) break;
				}
				//if (result == false) break;
			}
			
			
			//At this point the entire graph should have been mostly solved
			
			//println (global_pc.toString());
			//Take care of nonequality and concat
			//println ("Starting with not equality");
			//boolean handleNotResult = handleNots(g);
			boolean handleNotResult = handleNots(g);
			if (!handleNotResult) {
				//println ("returned no");
				if (PathCondition.flagSolved == false) {
					logger.info ("path condition to be solved");
					logger.info (global_pc.toString());
					loops++;
					long starttime = System.currentTimeMillis();
					boolean int_result = scg.isSatisfiable(global_pc);
					long temp_duration = System.currentTimeMillis() - starttime;
					int_duration = int_duration + temp_duration;
					duration = duration - temp_duration;
					
					if (int_result) {
						scg.solve(global_pc);
						PathCondition.flagSolved = true;
						mapAutomaton = null;
						restart = true;
					}
					else {
						//println ("[isSat] handled isnots, path condition could not be solved");
						return false;
					}
				}
				else {
					//println ("[isSat] handled isnots, path condition did not change");
					return false;
				}
			}
			
			/*//println ("Proposed solutions: ");
			for (Vertex v: g.getVertices()) {
				//println (v.getName() + ": '" + v.getSolution() + "'");
			}*/
		}
		/*if (pc.header != null) {
			listOfConstraints.add(0, pc.header);
			memo.put(listOfConstraints, mapAutomaton);
		}*/
		
		return true;
	}
	
	private static boolean handleNots (StringGraph g) {
		int numberOfNots = 0;
		//println ("Start of handleNots");
		for (Edge e: g.getEdges()) {
			if (e instanceof EdgeNotEqual) {
				if (e.getSource().getSolution().equals(e.getDest().getSolution())) {
					//println (e.getSource().getName() + " (" + e.getSource().getSolution() + ") == " + e.getDest().getName() + " (" + e.getDest().getSolution() + ") and it shouldn't");
					if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
						numberOfNots++;
					}
				}
			}
			else if (e instanceof EdgeNotStartsWith) {
				if (e.getSource().getSolution().startsWith(e.getDest().getSolution())) {
					//println (e.getSource().getName() + " (" + e.getSource().getSolution() + ") startswith " + e.getDest().getName() + " (" + e.getDest().getSolution() + ") and it shouldn't");
					if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
						numberOfNots++;
					}
				}
			}
			else if (e instanceof EdgeNotEndsWith) {
				if (e.getSource().getSolution().endsWith(e.getDest().getSolution())) {
					if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
						numberOfNots++;
					}
				}
			}
			else if (e instanceof EdgeNotContains) {
				EdgeNotContains enc = (EdgeNotContains) e;
				if (enc.getSource().getSolution().contains(enc.getDest().getSolution())) {
					//println (enc.getSource().getSolution() + " contains " + enc.getDest().getSolution() + " and it should not");
					if (!enc.getSource().isConstant() && !enc.getDest().isConstant()) {
						numberOfNots++;
					}
				}
			}
			else if (e instanceof EdgeIndexOf) {
				EdgeIndexOf eio = (EdgeIndexOf) e;
				if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().contains(eio.getDest().getSolution())) {
					//println ("'" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not");
					if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
						numberOfNots++;
					}
				}
			}
			else if (e instanceof EdgeIndexOf2) {
				EdgeIndexOf2 eio = (EdgeIndexOf2) e;
				if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().indexOf(eio.getDest().getSolution(), eio.getIndex().getMinIndex().solutionInt()) > -1) {
					//println ("[EdgeIndexOf2] '" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not from " + eio.getIndex().getMinIndex().solution());
					if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
						numberOfNots++;
					}
				}
			}
			else if (e instanceof EdgeIndexOfChar) {
				EdgeIndexOfChar eio = (EdgeIndexOfChar) e;
				if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().contains(eio.getDest().getSolution())) {
					//println ("[EdgeIndexOfChar] '" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not");
					if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
						numberOfNots++;
					}
				}
			}
			else if (e instanceof EdgeLastIndexOfChar) {
				EdgeLastIndexOfChar eio = (EdgeLastIndexOfChar) e;
				if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().contains(eio.getDest().getSolution())) {
					//println ("'" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not");
					if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
						numberOfNots++;
					}
				}
			}
			else if (e instanceof EdgeIndexOfChar2) {
				EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e;
				if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().indexOf(eio.getDest().getSolution(), eio.getIndex().getMinDist().solutionInt()) > -1) {
					//println ("[EdgeIndexOfChar2] '" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' after " + eio.getIndex().getMinDist().solution() + " and it should not");
					if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
						numberOfNots++;
					}
				}
			}
		}
		//println ("numberOfNots: " + numberOfNots);
		/*if (numberOfNots == 0) {
			return true;
		}*/
		Map<Vertex, Automaton> copyOfMapAutomaton = null;
		if (mapAutomaton != null) {
			copyOfMapAutomaton = copyMapAutomaton();
		}
		
		
		int result = 0;
		while (true) {
			//println ("Starting with innerHandleNots");
			result = innerHandleNots(g, toBits(numberOfNots, 0));
			//println ("result: " + result);
			if (result  == 2) {
				numberOfNots++;
				//println ("Number of nots going up");
				continue;
			}
			if (PathCondition.flagSolved == false) {
				/*println ("first path condition not solved");
				loops++;
				long starttime = System.currentTimeMillis();
				boolean temp_result = scg.isSatisfiable(global_pc);
				long temp_dur = System.currentTimeMillis() - starttime;
				int_duration += temp_dur;
				duration -= temp_dur;
				if (temp_result) {
					//println ("first path solved and restarting");
					scg.solve(global_pc);
					PathCondition.flagSolved = true;
					continue;
				}
				else {
					//println ("[handleNots] handled isnots, path condition could not be solved");
					return false;
				}*/
				//println ("Not working for us: 0");
				return false;
			}
			int i = 1;
			boolean breakInnerLoop = false;
			//println ("Starting while loop...");
			while (i < numberOfNots && result == 0) {
				//println ("in while loop");
				if (PathCondition.flagSolved == false) {
					/*loops++;
					long starttime = System.currentTimeMillis();
					boolean temp_result = scg.isSatisfiable(global_pc);
					long temp_dur = System.currentTimeMillis() - starttime;
					int_duration += temp_dur;
					duration -= temp_dur;
					if (temp_result) {
						scg.solve(global_pc);
						PathCondition.flagSolved = true;
					}
					else {
						//println ("[isSat] handled isnots, path condition could not be solved");
						return false;
					}*/
					//println ("Not working for us: " + i);
					return false;
				}
				
				//println ("loop");
				mapAutomaton = copyOfMapAutomaton;
				//println ("numberOfNots " + numberOfNots + " i " +i );
				result = innerHandleNots(g, toBits(numberOfNots, i));
				if (result == 2) {
					numberOfNots++;
					breakInnerLoop = true;
					break;
				}
				i++;
			}
			if (breakInnerLoop == true) { //restart the service
				breakInnerLoop = false;
				continue;
			}
			break;
		}
		if (result == 0) return false;
		else return true;
	}
	
	private static Map<Vertex, Automaton> copyMapAutomaton () {
		Map<Vertex, Automaton> result = new HashMap<Vertex, Automaton>();
		
		for (Entry<Vertex, Automaton> entry: mapAutomaton.entrySet()) {
			Vertex newVertex = new Vertex (entry.getKey());
			Automaton newAutomaton = entry.getValue().clone();
			result.put(newVertex, newAutomaton);
		}
		return result;
	}
	
	private static boolean[] toBits (int length, int c) {
		//println (String.format("toBits (%d, %d)\n", length, c));
		boolean[] result = new boolean[length];
		int num = (int) c;
		int i = result.length - 1;
		int div = (int) Math.pow(2, length-1);
		//println ("div " + div);
		while (num > 0) {
			//println ("num " + num + " i " + i);
			int temp = num / div;
			//println (String.format("%d / %d = %d\n", num, div, temp));
			//println ("temp " + temp);
			num = num - div * temp;
			div = div / 2;
			if (temp == 1) result[i] = true;
			i--;
		}
		return result;
	}
	
	private static int innerHandleNots (StringGraph g, boolean[] bitArray) {
		boolean nonequalityFlipFlop = false;
		int indexBitArray = 0;
		boolean change = true;
		for (int i = 0; i < bitArray.length; i++) {
			SymbolicStringConstraintsGeneral.checkTimeOut();
			try {
				change = false;
				//TODO: Add last index of, and can optimise indexOf with dest as constant
				for (Edge e: g.getEdges()) {
					if (e instanceof EdgeNotEqual) {
						if (e.getSource().getSolution().equals(e.getDest().getSolution())) {
							//println (e.getSource().getName() + " (" + e.getSource().getSolution() + ") == " + e.getDest().getName() + " (" + e.getDest().getSolution() + ") and it shouldn't");
							if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
								//println ("Here 1");
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a = mapAutomaton.get(e.getSource());
									//a minus current solution
									a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
									if (a.isEmpty()) {
										//println ("[isSat] EdgeNotEqual gave empty");
										elimanateCurrentLengths();
										return 0;
									}
									mapAutomaton.put(e.getSource(), a);
									e.getSource().setSolution(a.getShortestExample(true));
									change = true;
									//println ("change = true");
									
									boolean propResult = propagateChange(e.getSource(), e.getDest());
									if (!propResult) return 0;
								}
								else {
									Automaton a = mapAutomaton.get(e.getDest());
									//a minus current solution
									a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
									if (a.isEmpty()) {
										//println ("[isSat] EdgeNotEqual gave empty");
										elimanateCurrentLengths();
										return 0;
									}
									mapAutomaton.put(e.getDest(), a);
									e.getDest().setSolution(a.getShortestExample(true));
									change = true;
	
									boolean propResult = propagateChange(e.getDest(), e.getSource());
									if (!propResult) return 0;
								}
							}
							else if (!e.getSource().isConstant()) {
								Automaton a = mapAutomaton.get(e.getSource());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotEqual gave empty");
									elimanateCurrentLengths();
									return 0;
								}
								mapAutomaton.put(e.getSource(), a);
								e.getSource().setSolution(a.getShortestExample(true));
								change = true;
								boolean propResult = propagateChange(e.getSource(), e.getDest());
								if (!propResult) return 0;
							}
							else if (!e.getDest().isConstant()) {
								Automaton a = mapAutomaton.get(e.getDest());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotEqual gave empty");
									elimanateCurrentLengths();
									return 0;
								}
								mapAutomaton.put(e.getDest(), a);
								e.getDest().setSolution(a.getShortestExample(true));
								change = true;
								boolean propResult = propagateChange(e.getDest(), e.getSource());
								if (!propResult) return 0;
							}
							else {
								//All is constant
								return 0;
							}
						}
					}
					else if (e instanceof EdgeNotStartsWith) {
						if (e.getSource().getSolution().startsWith(e.getDest().getSolution())) {
							logger.info (e.getSource().getName() + " (" + e.getSource().getSolution() + ") startswith " + e.getDest().getName() + " (" + e.getDest().getSolution() + ") and it shouldn't");
							if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
								//println ("Here 2");
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a = mapAutomaton.get(e.getSource());
									//a minus current solution
									a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
									if (a.isEmpty()) {
										//println ("[isSat] EdgeNotStartsWith gave empty");
										elimanateCurrentLengths();
										return 0;
									}
									mapAutomaton.put(e.getSource(), a);
									e.getSource().setSolution(a.getShortestExample(true));
									change = true;
									
									boolean propResult = propagateChange(e.getSource(), e.getDest());
									if (!propResult) return 0;
								}
								else {
									Automaton a = mapAutomaton.get(e.getDest());
									//a minus current solution
									a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
									if (a.isEmpty()) {
										//println ("[isSat] EdgeNotStartsWith gave empty");
										elimanateCurrentLengths();
										return 0;
									}
	
									mapAutomaton.put(e.getDest(), a);
									e.getDest().setSolution(a.getShortestExample(true));
									change = true;
	
									boolean propResult = propagateChange(e.getDest(), e.getSource());
									if (!propResult) return 0;
								}
							}
							else if (!e.getSource().isConstant()) {
								Automaton a = mapAutomaton.get(e.getSource());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotStartsWith gave empty");
									elimanateCurrentLengths();
									return 0;
								}
								mapAutomaton.put(e.getSource(), a);
								e.getSource().setSolution(a.getShortestExample(true));
								change = true;
								boolean propResult = propagateChange(e.getSource(), e.getDest());
								if (!propResult) return 0;
							}
							else if (!e.getDest().isConstant()) {
								Automaton a = mapAutomaton.get(e.getDest());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								mapAutomaton.put(e.getDest(), a);
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotStartsWith gave empty");
									elimanateCurrentLengths();
									return 0;
								}
	
								e.getDest().setSolution(a.getShortestExample(true));
								change = true;
								boolean propResult = propagateChange(e.getDest(), e.getSource());
								if (!propResult) return 0;
							}
							else {
								//All is constant
								return 0;
							}
						}
					}
					else if (e instanceof EdgeNotEndsWith) {
						if (e.getSource().getSolution().endsWith(e.getDest().getSolution())) {
							//println (e.getSource().getName() + " (" + e.getSource().getSolution() + ") endsWith " + e.getDest().getName() + " (" + e.getDest().getSolution() + ") and it shouldn't");
							if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a = mapAutomaton.get(e.getSource());
									//a minus current solution
									a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
									if (a.isEmpty()) {
										//println ("[isSat] EdgeNotEndsWith gave empty");
										elimanateCurrentLengths();
										return 0;
									}
	
									mapAutomaton.put(e.getSource(), a);
									e.getSource().setSolution(a.getShortestExample(true));
									change = true;
									
									boolean propResult = propagateChange(e.getSource(), e.getDest());
									if (!propResult) return 0;
								}
								else {
									Automaton a = mapAutomaton.get(e.getDest());
									//a minus current solution
									a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
									if (a.isEmpty()) {
										//println ("[isSat] EdgeNotEndsWith gave empty");
										elimanateCurrentLengths();
										return 0;
									}
	
									mapAutomaton.put(e.getDest(), a);
									e.getDest().setSolution(a.getShortestExample(true));
									change = true;
	
									boolean propResult = propagateChange(e.getDest(), e.getSource());
									if (!propResult) return 0;
								}
							}
							else if (!e.getSource().isConstant()) {
								Automaton a = mapAutomaton.get(e.getSource());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotEndsWith gave empty");
									elimanateCurrentLengths();
									return 0;
								}
								mapAutomaton.put(e.getSource(), a);
								e.getSource().setSolution(a.getShortestExample(true));
								change = true;
								boolean propResult = propagateChange(e.getSource(), e.getDest());
								if (!propResult) return 0;
							}
							else if (!e.getDest().isConstant()) {
								Automaton a = mapAutomaton.get(e.getDest());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotEndsWith gave empty");
									elimanateCurrentLengths();
									return 0;
								}
	
								mapAutomaton.put(e.getDest(), a);
								e.getDest().setSolution(a.getShortestExample(true));
								change = true;
								boolean propResult = propagateChange(e.getDest(), e.getSource());
								if (!propResult) return 0;
							}
							else {
								//All is constant
								return 0;
							}
						}
					}
					else if (e instanceof EdgeConcat) {
						EdgeConcat ec = (EdgeConcat) e;
						String concat = ec.getSources().get(0).getSolution().concat(ec.getSources().get(1).getSolution());
						Automaton a1 = Automaton.makeString(concat);
						Automaton a2 = mapAutomaton.get(ec.getDest());
						while (AutomatonExtra.intersection(a1, a2).isEmpty()) {
							//println ("Concat between " + ec.getSources().get(0).getName() + " and " + e.getSources().get(1).getName());
							//println ("does not work for solutions: '" + ec.getSources().get(0).getSolution() + "' and '" + ec.getSources().get(1).getSolution() +"'");
							Automaton source1 = mapAutomaton.get(ec.getSources().get(0));
							Automaton source2 = mapAutomaton.get(ec.getSources().get(1));
							String source1Solution = ec.getSources().get(0).getSolution();
							String source2Solution = ec.getSources().get(1).getSolution();
							// source1 minus current solution
							source1 = AutomatonExtra.minus(source1, Automaton.makeString(source1Solution));
							// source2 minus current solution
							source2 = AutomatonExtra.minus(source2, Automaton.makeString(source2Solution));
							mapAutomaton.put(ec.getSources().get(0), source1);
							mapAutomaton.put(ec.getSources().get(1), source2);
							if (source1.isEmpty()) return 0;
							if (source2.isEmpty()) return 0;
							if (!ec.getSources().get(0).isConstant()) {ec.getSources().get(0).setSolution(source1.getShortestExample(true));}
							if (!ec.getSources().get(1).isConstant()) {ec.getSources().get(1).setSolution(source2.getShortestExample(true));}
							boolean propresult = propagateChange(ec.getSources().get(0), ec.getDest());
							propresult = propresult && propagateChange(ec.getSources().get(1), ec.getDest());
							if (!propresult) return 0;
							
							//Apply lengths
							Automaton length1 = AutomatonExtra.lengthAutomaton(ec.getSources().get(0).getLength());
							Automaton length2 = AutomatonExtra.lengthAutomaton(ec.getSources().get(1).getLength());
							source1 = AutomatonExtra.intersection(mapAutomaton.get(ec.getSources().get(0)), length1);
							source2 = AutomatonExtra.intersection(mapAutomaton.get(ec.getSources().get(1)), length2);
							if (!ec.getSources().get(0).isConstant()) ec.getSources().get(0).setSolution(source1.getShortestExample(true));
							if (!ec.getSources().get(1).isConstant()) ec.getSources().get(1).setSolution(source2.getShortestExample(true));
							
							
							concat = ec.getSources().get(0).getSolution().concat(ec.getSources().get(1).getSolution());
							a1 = Automaton.makeString(concat);
							a2 = mapAutomaton.get(ec.getDest());
							change = true;
						}
					}
					else if (e instanceof EdgeNotContains) {
						EdgeNotContains enc = (EdgeNotContains) e;
						if (enc.getSource().getSolution().contains(enc.getDest().getSolution())) {
							if (!enc.getSource().isConstant() && !enc.getDest().isConstant()) {
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a1 = mapAutomaton.get(enc.getSource());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getSource().getSolution()));
									if (temp.isEmpty()) {
										//println ("[isSat] EdgeNotContains return false");
										return 0;
									}
									if (!enc.getSource().isConstant()) enc.getSource().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(enc.getSource(), temp);
									boolean propResult = propagateChange(enc.getSource(), enc.getDest());
									if (!propResult) {
										//println ("[isSat] EdgeNotContains return false");
										return 0;
									}
									
								}
								else {
									Automaton a1 = mapAutomaton.get(enc.getDest());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getDest().getSolution()));
									if (temp.isEmpty()) {
										//println ("[isSat] EdgeNotContains return false");
										return 0;
									}
									if (!enc.getDest().isConstant()) enc.getDest().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(enc.getDest(), temp);
									boolean propResult = propagateChange(enc.getDest(), enc.getSource());
									if (!propResult) {
										//println ("[isSat] EdgeNotContains return false");
										return 0;
									}
	
								}
							}
							else if (!enc.getSource().isConstant()) {
								Automaton a1 = mapAutomaton.get(enc.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getSource().getSolution()));
								if (temp.isEmpty()) {
									//println ("[isSat] EdgeNotContains return false");
									return 0;
								}
								if (!enc.getSource().isConstant()) enc.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(enc.getSource(), temp);
								boolean propResult = propagateChange(enc.getSource(), enc.getDest());
								if (!propResult) {
									//println ("[isSat] EdgeNotContains return false");
									return 0;
								}
							}
							else if (!enc.getDest().isConstant()) {
								Automaton a1 = mapAutomaton.get(enc.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getDest().getSolution()));
								if (temp.isEmpty()) {
									//println ("[isSat] EdgeNotContains return false");
									return 0;
								}
								if (!enc.getDest().isConstant()) enc.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(enc.getDest(), temp);
								boolean propResult = propagateChange(enc.getDest(), enc.getSource());
								if (!propResult) {
									//println ("[isSat] EdgeNotContains return false");
									return 0;
								}
							}
							else {
								//println ("[isSat] EdgeNotContains return false");
								return 0;
							}
							
							change = true;
						}
					}
					else if (e instanceof EdgeIndexOf) { //TODO: Major patch up need for cases, where index was guessed wrong
						EdgeIndexOf eio = (EdgeIndexOf) e;
						if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().contains(eio.getDest().getSolution())) {
							//println ("'" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not");
							if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a1 = mapAutomaton.get(eio.getSource());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
									if (temp.isEmpty()) return 0;
									if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getSource(), temp);
									boolean propResult = propagateChange(eio.getSource(), eio.getDest());
									if (!propResult) return 0;
									
								}
								else {
									Automaton a1 = mapAutomaton.get(eio.getDest());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
									if (temp.isEmpty()) return 0;
									if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getDest(), temp);
									boolean propResult = propagateChange(eio.getDest(), eio.getSource());
									if (!propResult) return 0;
	
								}
							}
							else if (!eio.getSource().isConstant()) {
								//println ("branch 2");
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) {
									//println ("here 1");
									LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
									loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
									global_pc._addDet(loic);
									return 0;
								}
								
								/* Check if source can't contain destination */
								Automaton temp_destination = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(eio.getDest().getSolution())).concatenate(AutomatonExtra.makeAnyStringFixed()); 
								Automaton temp2 = AutomatonExtra.minus(a1, temp_destination);
								if (temp2.isEmpty()) {
									LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
									loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
									global_pc._addDet(loic);
									return 0;
								}
								
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) {
									//println ("here 2");
									LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
									loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
									global_pc._addDet(loic);
									return 0;
								}
							}
							else if (!eio.getDest().isConstant()) {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) return 0;
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) return 0;
							}
							else {
								//Everything is constant
								return 0;
							}
							
							change = true;
						}
						else if (eio.getIndex().solution() != -1 && eio.getSource().getSolution().indexOf(eio.getDest().getSolution()) < eio.getIndex().solution()) {
							//TODO: What if indexOf == -1?
							//println ("'" + eio.getSource().getSolution() + "' indexof '" + eio.getDest().getSolution() + "' == " + eio.getSource().getSolution().indexOf(eio.getDest().getSolution()) +" and it should not");
							int indexOf = eio.getSource().getSolution().indexOf(eio.getDest().getSolution());
							if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a1 = mapAutomaton.get(eio.getSource());
									Automaton toBeRemoved = AutomatonExtra.lengthAutomaton(indexOf).concatenate(Automaton.makeChar(eio.getDest().getSolution().charAt(0)).concatenate(AutomatonExtra.lengthAutomaton(e.getSource().getLength() - indexOf - 1)));
									/*println (String.format ("1 '%s'", AutomatonExtra.lengthAutomaton(indexOf).getShortestExample(true)));
									//println (String.format ("2 '%s'", Automaton.makeChar(eio.getDest().getSolution().charAt(0)).getShortestExample(true)));
									//println (String.format ("3 '%s'", AutomatonExtra.lengthAutomaton(e.getSource().getLength() - indexOf - 1).getShortestExample(true)));
									//println (String.format ("ToBeRemoved '%s'", toBeRemoved.getShortestExample(true)));*/
									Automaton temp = AutomatonExtra.minus (a1, toBeRemoved);
									if (temp.isEmpty()) return 0;
									if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getSource(), temp);
									boolean propResult = propagateChange(eio.getSource(), eio.getDest());
									if (!propResult) return 0;
									
								}
								else {
									Automaton a1 = mapAutomaton.get(eio.getDest());
									Automaton toBeRemoved = Automaton.makeChar(eio.getSource().getSolution().charAt(indexOf)).concatenate(AutomatonExtra.lengthAutomaton(e.getDest().getLength() - 1));
									Automaton temp = AutomatonExtra.minus (a1, toBeRemoved);
									if (temp.isEmpty()) return 0;
									if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getDest(), temp);
									boolean propResult = propagateChange(eio.getDest(), eio.getSource());
									if (!propResult) return 0;
	
								}
							}
							else if (!eio.getSource().isConstant()) { //TODO: Need to update
								//println ("branch 2");
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) {
									//println ("here 1");
									LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
									loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
									global_pc._addDet(loic);
									return 0;
								}
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) {
									//println ("here 2");
									LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
									loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE, new IntegerConstant(eio.getIndex().solution())));
									global_pc._addDet(loic);
									return 0;
								}
							}
							else if (!eio.getDest().isConstant()) {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) return 0;
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) return 0;
							}
							else {
								//Everything is constant
								return 0;
							}
							
							change = true;
						}
					}
					else if (e instanceof EdgeIndexOf2) {
						EdgeIndexOf2 eio = (EdgeIndexOf2) e;
						if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().indexOf(eio.getDest().getSolution(), eio.getIndex().getMinIndex().solutionInt()) > -1) {
							//println ("[EdgeIndexOf2] '" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not from " + eio.getIndex().getMinIndex().solution());
							if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a1 = mapAutomaton.get(eio.getSource());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
									if (temp.isEmpty()) return 0; //Maybe remove the possibility of -1?
									if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getSource(), temp);
									boolean propResult = propagateChange(eio.getSource(), eio.getDest());
									if (!propResult) return 0;
									
								}
								else {
									Automaton a1 = mapAutomaton.get(eio.getDest());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
									if (temp.isEmpty()) return 0;
									if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getDest(), temp);
									boolean propResult = propagateChange(eio.getDest(), eio.getSource());
									if (!propResult) return 0;
	
								}
							}
							else if (!eio.getSource().isConstant()) {
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) return 0;
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) return 0;
							}
							else if (!eio.getDest().isConstant()) {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) return 0;
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) return 0;
							}
							else {
								//Everything is constant
								return 0;
							}
							
							change = true;
						}
					}
					else if (e instanceof EdgeIndexOfChar) {
						EdgeIndexOfChar eio = (EdgeIndexOfChar) e;
						if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().contains(eio.getDest().getSolution())) {
							//println ("[EdgeIndexOfChar] '" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not");
							if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
								//println ("[EdgeIndexOfChar] branch 1");
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a1 = mapAutomaton.get(eio.getSource());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
									if (temp.isEmpty()) return 0;
									if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getSource(), temp);
									boolean propResult = propagateChange(eio.getSource(), eio.getDest());
									if (!propResult) return 0;
									
								}
								else {
									Automaton a1 = mapAutomaton.get(eio.getDest());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
									if (temp.isEmpty()) return 0;
									if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getDest(), temp);
									boolean propResult = propagateChange(eio.getDest(), eio.getSource());
									if (!propResult) return 0;
	
								}
							}
							else if (!eio.getSource().isConstant()) {
								//println ("[EdgeIndexOfChar] branch 2");
								Automaton a1 = mapAutomaton.get(eio.getSource());
								/*Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) return false;
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) return false;*/
								Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(eio.getDest().getSolution())).concatenate(AutomatonExtra.makeAnyStringFixed());
								//println ("[EdgeIndexOfChar] temp example '" + temp.getShortestExample(true) + "'");
								Automaton newA1 = AutomatonExtra.minus(a1, temp);
								if (newA1.isEmpty()) {
									//println ("[EdgeIndexOfChar] returning false");
									return 0;
								}
								eio.getSource().setSolution(newA1.getShortestExample(true));
								//println ("eio.getSource().getSolution(): '" + eio.getSource().getSolution() + "'");
								mapAutomaton.put(eio.getSource(), newA1);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) {
									//println ("[EdgeIndexOfChar] propegation returning false");
									return 0;
								}
							}
							else if (!eio.getDest().isConstant()) {
								//println ("[EdgeIndexOfChar] branch 3");
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) return 0;
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) return 0;
							}
							else {
								//Everything is constant
								return 0;
							}
							
							change = true;
						}
					}
					else if (e instanceof EdgeLastIndexOfChar) {
						EdgeLastIndexOfChar eio = (EdgeLastIndexOfChar) e;
						if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().contains(eio.getDest().getSolution())) {
							//println ("'" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not");
							if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a1 = mapAutomaton.get(eio.getSource());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
									if (temp.isEmpty()) {
										//println ("[isSat] EdgeLastIndexOfChar return false");
										return 0;
									}
									if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getSource(), temp);
									boolean propResult = propagateChange(eio.getSource(), eio.getDest());
									if (!propResult) {
										//println ("[isSat] EdgeLastIndexOfChar return false");
										return 0;
									}
									
								}
								else {
									Automaton a1 = mapAutomaton.get(eio.getDest());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
									if (temp.isEmpty()) {
										//println ("[isSat] EdgeLastIndexOfChar return false");
										return 0;
									}
									if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getDest(), temp);
									boolean propResult = propagateChange(eio.getDest(), eio.getSource());
									if (!propResult) {
										//println ("[isSat] EdgeLastIndexOfChar return false");
										return 0;
									}
	
								}
							}
							else if (!eio.getSource().isConstant()) {
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) {
									//println ("[isSat] EdgeLastIndexOfChar return false");
									return 0;
								}
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) {
									//println ("[isSat] EdgeLastIndexOfChar return false");
									return 0;
								}
							}
							else if (!eio.getDest().isConstant()) {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) {
									//println ("[isSat] EdgeLastIndexOfChar return false");
									return 0;
								}
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) {
									//println ("[isSat] EdgeLastIndexOfChar return false");
									return 0;
								}
							}
							else {
								//println ("[isSat] EdgeLastIndexOfChar return false");
								return 0;
							}
							
							change = true;
						}
					}
					else if (e instanceof EdgeIndexOfChar2) {
						EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e;
						if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().indexOf(eio.getDest().getSolution(), eio.getIndex().getMinDist().solutionInt()) > -1) {
							logger.info ("[EdgeIndexOfChar2] '" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' after " + eio.getIndex().getMinDist().solution() + " and it should not");
							if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
								nonequalityFlipFlop = bitArray[indexBitArray++];
								if (nonequalityFlipFlop == false) {
									Automaton a1 = mapAutomaton.get(eio.getSource());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
									if (temp.isEmpty()) return 0;
									if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getSource(), temp);
									boolean propResult = propagateChange(eio.getSource(), eio.getDest());
									if (!propResult) return 0;
									
								}
								else {
									Automaton a1 = mapAutomaton.get(eio.getDest());
									Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
									if (temp.isEmpty()) return 0;
									if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
									mapAutomaton.put(eio.getDest(), temp);
									boolean propResult = propagateChange(eio.getDest(), eio.getSource());
									if (!propResult) return 0;
	
								}
							}
							else if (!eio.getSource().isConstant()) {
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) return 0;
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) return 0;
							}
							else if (!eio.getDest().isConstant()) {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) return 0;
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) return 0;
							}
							else {
								//Everything is constant
								return 0;
							}
							
							change = true;
						}
					}
				}
			} catch (ArrayIndexOutOfBoundsException e) {
				//number of nots was incorrect
				return 2;
			}
		}
		if (change == true) {
			//number of nots was incorrect
			return 2;
		}
		return 1;
	}
	
	
	private static boolean handleNotsSpeedUp (StringGraph g) {
		int nonequalityFlipFlop = 0;
		boolean change = true;
		while (change) {
			change = false;
			//TODO: Add last index of, and can optimise indexOf with dest as constant
			for (Edge e: g.getEdges()) {
				if (e instanceof EdgeNotEqual) {
					if (e.getSource().getSolution().equals(e.getDest().getSolution())) {
						//println (e.getSource().getName() + " (" + e.getSource().getSolution() + ") == " + e.getDest().getName() + " (" + e.getDest().getSolution() + ") and it shouldn't");
						if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
							if (nonequalityFlipFlop == 0) {
								Automaton a = mapAutomaton.get(e.getSource());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotEqual gave empty");
									elimanateCurrentLengths();
									return false;
								}
								mapAutomaton.put(e.getSource(), a);
								e.getSource().setSolution(a.getShortestExample(true));
								change = true;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
								boolean propResult = propagateChange(e.getSource(), e.getDest());
								if (!propResult) return false;
							}
							else {
								Automaton a = mapAutomaton.get(e.getDest());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotEqual gave empty");
									elimanateCurrentLengths();
									return false;
								}
								mapAutomaton.put(e.getDest(), a);
								e.getDest().setSolution(a.getShortestExample(true));
								change = true;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
								boolean propResult = propagateChange(e.getDest(), e.getSource());
								if (!propResult) return false;
							}
						}
						else if (!e.getSource().isConstant()) {
							Automaton a = mapAutomaton.get(e.getSource());
							//a minus current solution
							a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
							if (a.isEmpty()) {
								//println ("[isSat] EdgeNotEqual gave empty");
								elimanateCurrentLengths();
								return false;
							}
							mapAutomaton.put(e.getSource(), a);
							e.getSource().setSolution(a.getShortestExample(true));
							change = true;
							boolean propResult = propagateChange(e.getSource(), e.getDest());
							if (!propResult) return false;
						}
						else if (!e.getDest().isConstant()) {
							Automaton a = mapAutomaton.get(e.getDest());
							//a minus current solution
							a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
							if (a.isEmpty()) {
								//println ("[isSat] EdgeNotEqual gave empty");
								elimanateCurrentLengths();
								return false;
							}
							mapAutomaton.put(e.getDest(), a);
							e.getDest().setSolution(a.getShortestExample(true));
							change = true;
							boolean propResult = propagateChange(e.getDest(), e.getSource());
							if (!propResult) return false;
						}
						else {
							//All is constant
							return false;
						}
					}
				}
				else if (e instanceof EdgeNotStartsWith) {
					if (e.getSource().getSolution().startsWith(e.getDest().getSolution())) {
						//println (e.getSource().getName() + " (" + e.getSource().getSolution() + ") startswith " + e.getDest().getName() + " (" + e.getDest().getSolution() + ") and it shouldn't");
						if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
							if (nonequalityFlipFlop == 0) {
								Automaton a = mapAutomaton.get(e.getSource());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotStartsWith gave empty");
									elimanateCurrentLengths();
									return false;
								}
								mapAutomaton.put(e.getSource(), a);
								e.getSource().setSolution(a.getShortestExample(true));
								change = true;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
								boolean propResult = propagateChange(e.getSource(), e.getDest());
								if (!propResult) return false;
							}
							else {
								Automaton a = mapAutomaton.get(e.getDest());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotStartsWith gave empty");
									elimanateCurrentLengths();
									return false;
								}

								mapAutomaton.put(e.getDest(), a);
								e.getDest().setSolution(a.getShortestExample(true));
								change = true;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
								boolean propResult = propagateChange(e.getDest(), e.getSource());
								if (!propResult) return false;
							}
						}
						else if (!e.getSource().isConstant()) {
							Automaton a = mapAutomaton.get(e.getSource());
							//a minus current solution
							a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
							if (a.isEmpty()) {
								//println ("[isSat] EdgeNotStartsWith gave empty");
								elimanateCurrentLengths();
								return false;
							}
							mapAutomaton.put(e.getSource(), a);
							e.getSource().setSolution(a.getShortestExample(true));
							change = true;
							boolean propResult = propagateChange(e.getSource(), e.getDest());
							if (!propResult) return false;
						}
						else if (!e.getDest().isConstant()) {
							Automaton a = mapAutomaton.get(e.getDest());
							//a minus current solution
							a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
							mapAutomaton.put(e.getDest(), a);
							if (a.isEmpty()) {
								//println ("[isSat] EdgeNotStartsWith gave empty");
								elimanateCurrentLengths();
								return false;
							}

							e.getDest().setSolution(a.getShortestExample(true));
							change = true;
							boolean propResult = propagateChange(e.getDest(), e.getSource());
							if (!propResult) return false;
						}
						else {
							//All is constant
							return false;
						}
					}
				}
				else if (e instanceof EdgeNotEndsWith) {
					if (e.getSource().getSolution().endsWith(e.getDest().getSolution())) {
						//println (e.getSource().getName() + " (" + e.getSource().getSolution() + ") endsWith " + e.getDest().getName() + " (" + e.getDest().getSolution() + ") and it shouldn't");
						if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
							if (nonequalityFlipFlop == 0) {
								Automaton a = mapAutomaton.get(e.getSource());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotEndsWith gave empty");
									elimanateCurrentLengths();
									return false;
								}

								mapAutomaton.put(e.getSource(), a);
								e.getSource().setSolution(a.getShortestExample(true));
								change = true;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
								boolean propResult = propagateChange(e.getSource(), e.getDest());
								if (!propResult) return false;
							}
							else {
								Automaton a = mapAutomaton.get(e.getDest());
								//a minus current solution
								a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
								if (a.isEmpty()) {
									//println ("[isSat] EdgeNotEndsWith gave empty");
									elimanateCurrentLengths();
									return false;
								}

								mapAutomaton.put(e.getDest(), a);
								e.getDest().setSolution(a.getShortestExample(true));
								change = true;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
								boolean propResult = propagateChange(e.getDest(), e.getSource());
								if (!propResult) return false;
							}
						}
						else if (!e.getSource().isConstant()) {
							Automaton a = mapAutomaton.get(e.getSource());
							//a minus current solution
							a = AutomatonExtra.intersection(a, Automaton.makeString(e.getSource().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
							if (a.isEmpty()) {
								//println ("[isSat] EdgeNotEndsWith gave empty");
								elimanateCurrentLengths();
								return false;
							}
							mapAutomaton.put(e.getSource(), a);
							e.getSource().setSolution(a.getShortestExample(true));
							change = true;
							boolean propResult = propagateChange(e.getSource(), e.getDest());
							if (!propResult) return false;
						}
						else if (!e.getDest().isConstant()) {
							Automaton a = mapAutomaton.get(e.getDest());
							//a minus current solution
							a = AutomatonExtra.intersection(a, Automaton.makeString(e.getDest().getSolution()).complement().intersection(AutomatonExtra.makeAnyStringFixed()));
							if (a.isEmpty()) {
								//println ("[isSat] EdgeNotEndsWith gave empty");
								elimanateCurrentLengths();
								return false;
							}

							mapAutomaton.put(e.getDest(), a);
							e.getDest().setSolution(a.getShortestExample(true));
							change = true;
							boolean propResult = propagateChange(e.getDest(), e.getSource());
							if (!propResult) return false;
						}
						else {
							//All is constant
							return false;
						}
					}
				}
				else if (e instanceof EdgeConcat) {
					EdgeConcat ec = (EdgeConcat) e;
					String concat = ec.getSources().get(0).getSolution().concat(ec.getSources().get(1).getSolution());
					Automaton a1 = Automaton.makeString(concat);
					Automaton a2 = mapAutomaton.get(ec.getDest());
					while (AutomatonExtra.intersection(a1, a2).isEmpty()) {
						//println ("Concat between " + ec.getSources().get(0).getName() + " and " + e.getSources().get(1).getName());
						//println ("does not work for solutions: '" + ec.getSources().get(0).getSolution() + "' and '" + ec.getSources().get(1).getSolution() +"'");
						Automaton source1 = mapAutomaton.get(ec.getSources().get(0));
						Automaton source2 = mapAutomaton.get(ec.getSources().get(1));
						String source1Solution = ec.getSources().get(0).getSolution();
						String source2Solution = ec.getSources().get(1).getSolution();
						// source1 minus current solution
						source1 = AutomatonExtra.minus(source1, Automaton.makeString(source1Solution));
						// source2 minus current solution
						source2 = AutomatonExtra.minus(source2, Automaton.makeString(source2Solution));
						mapAutomaton.put(ec.getSources().get(0), source1);
						mapAutomaton.put(ec.getSources().get(1), source2);
						if (source1.isEmpty()) return false;
						if (source2.isEmpty()) return false;
						if (!ec.getSources().get(0).isConstant()) {ec.getSources().get(0).setSolution(source1.getShortestExample(true));}
						if (!ec.getSources().get(1).isConstant()) {ec.getSources().get(1).setSolution(source2.getShortestExample(true));}
						boolean propresult = propagateChange(ec.getSources().get(0), ec.getDest());
						propresult = propresult && propagateChange(ec.getSources().get(1), ec.getDest());
						if (!propresult) return false;
						
						//Apply lengths
						Automaton length1 = AutomatonExtra.lengthAutomaton(ec.getSources().get(0).getLength());
						Automaton length2 = AutomatonExtra.lengthAutomaton(ec.getSources().get(1).getLength());
						source1 = AutomatonExtra.intersection(mapAutomaton.get(ec.getSources().get(0)), length1);
						source2 = AutomatonExtra.intersection(mapAutomaton.get(ec.getSources().get(1)), length2);
						if (!ec.getSources().get(0).isConstant()) ec.getSources().get(0).setSolution(source1.getShortestExample(true));
						if (!ec.getSources().get(1).isConstant()) ec.getSources().get(1).setSolution(source2.getShortestExample(true));
						
						
						concat = ec.getSources().get(0).getSolution().concat(ec.getSources().get(1).getSolution());
						a1 = Automaton.makeString(concat);
						a2 = mapAutomaton.get(ec.getDest());
						change = true;
					}
				}
				else if (e instanceof EdgeNotContains) {
					EdgeNotContains enc = (EdgeNotContains) e;
					if (enc.getSource().getSolution().contains(enc.getDest().getSolution())) {
						//println (enc.getSource().getSolution() + " contains " + enc.getDest().getSolution() + " and it should not");
						if (!enc.getSource().isConstant() && !enc.getDest().isConstant()) {
							if (nonequalityFlipFlop == 0) {
								Automaton a1 = mapAutomaton.get(enc.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getSource().getSolution()));
								if (temp.isEmpty()) {
									//println ("[isSat] EdgeNotContains return false");
									return false;
								}
								if (!enc.getSource().isConstant()) enc.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(enc.getSource(), temp);
								boolean propResult = propagateChange(enc.getSource(), enc.getDest());
								if (!propResult) {
									//println ("[isSat] EdgeNotContains return false");
									return false;
								}
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
							else {
								Automaton a1 = mapAutomaton.get(enc.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getDest().getSolution()));
								if (temp.isEmpty()) {
									//println ("[isSat] EdgeNotContains return false");
									return false;
								}
								if (!enc.getDest().isConstant()) enc.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(enc.getDest(), temp);
								boolean propResult = propagateChange(enc.getDest(), enc.getSource());
								if (!propResult) {
									//println ("[isSat] EdgeNotContains return false");
									return false;
								}
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
						}
						else if (!enc.getSource().isConstant()) {
							Automaton a1 = mapAutomaton.get(enc.getSource());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getSource().getSolution()));
							if (temp.isEmpty()) {
								//println ("[isSat] EdgeNotContains return false");
								return false;
							}
							if (!enc.getSource().isConstant()) enc.getSource().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(enc.getSource(), temp);
							boolean propResult = propagateChange(enc.getSource(), enc.getDest());
							if (!propResult) {
								//println ("[isSat] EdgeNotContains return false");
								return false;
							}
						}
						else if (!enc.getDest().isConstant()) {
							Automaton a1 = mapAutomaton.get(enc.getDest());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getDest().getSolution()));
							if (temp.isEmpty()) {
								//println ("[isSat] EdgeNotContains return false");
								return false;
							}
							if (!enc.getDest().isConstant()) enc.getDest().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(enc.getDest(), temp);
							boolean propResult = propagateChange(enc.getDest(), enc.getSource());
							if (!propResult) {
								//println ("[isSat] EdgeNotContains return false");
								return false;
							}
						}
						else {
							//println ("[isSat] EdgeNotContains return false");
							return false;
						}
						
						change = true;
					}
				}
				else if (e instanceof EdgeIndexOf) {
					EdgeIndexOf eio = (EdgeIndexOf) e;
					if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().contains(eio.getDest().getSolution())) {
						//println ("'" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not");
						if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
							if (nonequalityFlipFlop == 0) {
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) return false;
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
							else {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) return false;
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
						}
						else if (!eio.getSource().isConstant()) {
							Automaton a1 = mapAutomaton.get(eio.getSource());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
							if (temp.isEmpty()) return false;
							if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getSource(), temp);
							boolean propResult = propagateChange(eio.getSource(), eio.getDest());
							if (!propResult) return false;
						}
						else if (!eio.getDest().isConstant()) {
							Automaton a1 = mapAutomaton.get(eio.getDest());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
							if (temp.isEmpty()) return false;
							if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getDest(), temp);
							boolean propResult = propagateChange(eio.getDest(), eio.getSource());
							if (!propResult) return false;
						}
						else {
							//Everything is constant
							return false;
						}
						
						change = true;
					}
				}
				else if (e instanceof EdgeIndexOf2) {
					EdgeIndexOf2 eio = (EdgeIndexOf2) e;
					if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().indexOf(eio.getDest().getSolution(), eio.getIndex().getMinIndex().solutionInt()) > -1) {
						//println ("[EdgeIndexOf2] '" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not from " + eio.getIndex().getMinIndex().solution());
						if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
							if (nonequalityFlipFlop == 0) {
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) return false; //Maybe remove the possibility of -1?
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
							else {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) return false;
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
						}
						else if (!eio.getSource().isConstant()) {
							Automaton a1 = mapAutomaton.get(eio.getSource());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
							if (temp.isEmpty()) return false;
							if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getSource(), temp);
							boolean propResult = propagateChange(eio.getSource(), eio.getDest());
							if (!propResult) return false;
						}
						else if (!eio.getDest().isConstant()) {
							Automaton a1 = mapAutomaton.get(eio.getDest());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
							if (temp.isEmpty()) return false;
							if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getDest(), temp);
							boolean propResult = propagateChange(eio.getDest(), eio.getSource());
							if (!propResult) return false;
						}
						else {
							//Everything is constant
							return false;
						}
						
						change = true;
					}
				}
				else if (e instanceof EdgeIndexOfChar) {
					EdgeIndexOfChar eio = (EdgeIndexOfChar) e;
					if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().contains(eio.getDest().getSolution())) {
						//println ("[EdgeIndexOfChar] '" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not");
						if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
							//println ("[EdgeIndexOfChar] branch 1");
							if (nonequalityFlipFlop == 0) {
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) return false;
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
							else {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) return false;
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
						}
						else if (!eio.getSource().isConstant()) {
							//println ("[EdgeIndexOfChar] branch 2");
							Automaton a1 = mapAutomaton.get(eio.getSource());
							/*Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
							if (temp.isEmpty()) return false;
							if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getSource(), temp);
							boolean propResult = propagateChange(eio.getSource(), eio.getDest());
							if (!propResult) return false;*/
							Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(eio.getDest().getSolution())).concatenate(AutomatonExtra.makeAnyStringFixed());
							//println ("[EdgeIndexOfChar] temp example '" + temp.getShortestExample(true) + "'");
							Automaton newA1 = AutomatonExtra.minus(a1, temp);
							if (newA1.isEmpty()) {
								//println ("[EdgeIndexOfChar] returning false");
								return false;
							}
							eio.getSource().setSolution(newA1.getShortestExample(true));
							//println ("eio.getSource().getSolution(): '" + eio.getSource().getSolution() + "'");
							mapAutomaton.put(eio.getSource(), newA1);
							boolean propResult = propagateChange(eio.getSource(), eio.getDest());
							if (!propResult) {
								//println ("[EdgeIndexOfChar] propegation returning false");
								return false;
							}
						}
						else if (!eio.getDest().isConstant()) {
							//println ("[EdgeIndexOfChar] branch 3");
							Automaton a1 = mapAutomaton.get(eio.getDest());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
							if (temp.isEmpty()) return false;
							if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getDest(), temp);
							boolean propResult = propagateChange(eio.getDest(), eio.getSource());
							if (!propResult) return false;
						}
						else {
							//Everything is constant
							return false;
						}
						
						change = true;
					}
				}
				else if (e instanceof EdgeLastIndexOfChar) {
					EdgeLastIndexOfChar eio = (EdgeLastIndexOfChar) e;
					if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().contains(eio.getDest().getSolution())) {
						//println ("'" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' and it should not");
						if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
							if (nonequalityFlipFlop == 0) {
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) {
									//println ("[isSat] EdgeLastIndexOfChar return false");
									return false;
								}
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) {
									//println ("[isSat] EdgeLastIndexOfChar return false");
									return false;
								}
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
							else {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) {
									//println ("[isSat] EdgeLastIndexOfChar return false");
									return false;
								}
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) {
									//println ("[isSat] EdgeLastIndexOfChar return false");
									return false;
								}
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
						}
						else if (!eio.getSource().isConstant()) {
							Automaton a1 = mapAutomaton.get(eio.getSource());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
							if (temp.isEmpty()) {
								//println ("[isSat] EdgeLastIndexOfChar return false");
								return false;
							}
							if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getSource(), temp);
							boolean propResult = propagateChange(eio.getSource(), eio.getDest());
							if (!propResult) {
								//println ("[isSat] EdgeLastIndexOfChar return false");
								return false;
							}
						}
						else if (!eio.getDest().isConstant()) {
							Automaton a1 = mapAutomaton.get(eio.getDest());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
							if (temp.isEmpty()) {
								//println ("[isSat] EdgeLastIndexOfChar return false");
								return false;
							}
							if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getDest(), temp);
							boolean propResult = propagateChange(eio.getDest(), eio.getSource());
							if (!propResult) {
								//println ("[isSat] EdgeLastIndexOfChar return false");
								return false;
							}
						}
						else {
							//println ("[isSat] EdgeLastIndexOfChar return false");
							return false;
						}
						
						change = true;
					}
				}
				else if (e instanceof EdgeIndexOfChar2) {
					EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e;
					if (eio.getIndex().solution() == -1 && eio.getSource().getSolution().indexOf(eio.getDest().getSolution(), eio.getIndex().getMinDist().solutionInt()) > -1) {
						//println ("[EdgeIndexOfChar2] '" + eio.getSource().getSolution() + "' contains '" + eio.getDest().getSolution() + "' after " + eio.getIndex().getMinDist().solution() + " and it should not");
						if (!eio.getSource().isConstant() && !eio.getDest().isConstant()) {
							if (nonequalityFlipFlop == 0) {
								Automaton a1 = mapAutomaton.get(eio.getSource());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
								if (temp.isEmpty()) return false;
								if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getSource(), temp);
								boolean propResult = propagateChange(eio.getSource(), eio.getDest());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
							else {
								Automaton a1 = mapAutomaton.get(eio.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
								if (temp.isEmpty()) return false;
								if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(eio.getDest(), temp);
								boolean propResult = propagateChange(eio.getDest(), eio.getSource());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
						}
						else if (!eio.getSource().isConstant()) {
							Automaton a1 = mapAutomaton.get(eio.getSource());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getSource().getSolution()));
							if (temp.isEmpty()) return false;
							if (!eio.getSource().isConstant()) eio.getSource().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getSource(), temp);
							boolean propResult = propagateChange(eio.getSource(), eio.getDest());
							if (!propResult) return false;
						}
						else if (!eio.getDest().isConstant()) {
							Automaton a1 = mapAutomaton.get(eio.getDest());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(eio.getDest().getSolution()));
							if (temp.isEmpty()) return false;
							if (!eio.getDest().isConstant()) eio.getDest().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(eio.getDest(), temp);
							boolean propResult = propagateChange(eio.getDest(), eio.getSource());
							if (!propResult) return false;
						}
						else {
							//Everything is constant
							return false;
						}
						
						change = true;
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handle (Edge e) {
		if (e instanceof EdgeStartsWith) {
			return handleEdgeStartsWith ((EdgeStartsWith) e);
		}
		else if (e instanceof EdgeNotStartsWith) {
			return handleEdgeNotStartsWith ((EdgeNotStartsWith) e);
		}
		else if (e instanceof EdgeEndsWith) {
			return handleEdgeEndsWith ((EdgeEndsWith) e);
		}
		else if (e instanceof EdgeNotEndsWith) {
			return handleEdgeNotEndsWith ((EdgeNotEndsWith) e);
		}
		else if (e instanceof EdgeCharAt) {
			return handleEdgeCharAt((EdgeCharAt) e);
		}
		else if (e instanceof EdgeConcat) {
			return handleEdgeConcat((EdgeConcat) e);
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
		else if (e instanceof EdgeLastIndexOf) {
			return handleEdgeLastIndexOf((EdgeLastIndexOf) e);
		}
		else if (e instanceof EdgeLastIndexOfChar) {
			return handleEdgeLastIndexOfChar((EdgeLastIndexOfChar) e);
		}
		else if (e instanceof EdgeLastIndexOfChar2) {
			return handleEdgeLastIndexOfChar2((EdgeLastIndexOfChar2) e);
		}
		else if (e instanceof EdgeContains) {
			return handleEdgeContains((EdgeContains) e);
		}
		else if (e instanceof EdgeNotContains) {
			return handleEdgeNotContains((EdgeNotContains) e);
		}
		else if (e instanceof EdgeSubstring1Equal) {
			return handleEdgeSubstring1Equal((EdgeSubstring1Equal) e);
		}
		else if (e instanceof EdgeSubstring2Equal) {
			return handleEdgeSubstring2Equal((EdgeSubstring2Equal) e);
		}
		else if (e instanceof EdgeTrimEqual) {
			return handleEdgeTrimEqual((EdgeTrimEqual) e);
		}
		else if (e instanceof EdgeNotEqual) {
			return true;
		}
		else if (e instanceof EdgeReplaceCharChar) {
			return handleEdgeReplaceCharChar((EdgeReplaceCharChar) e);
		}
		else {
			throw new RuntimeException("No handler for this edge: " + e.getClass());
		}
	}
	
	private static boolean propagateChange (Vertex vertexThatHasChanged, Vertex vertexComingFrom) {
		if (!PathCondition.flagSolved) {
			//println ("[propagateChange] Path condition is need of solving");
			return false;
		}
		List<Vertex> neighbours = global_graph.getNeighbours(vertexThatHasChanged);
		for (Vertex v: neighbours) {
			if (v.equals(vertexComingFrom)) continue;
			for (Edge e: global_graph.getEdges()) {
				if (e instanceof EdgeConcat) {
					if ((e.getSources().get(0).equals(v) || e.getSources().get(1).equals(v) || e.getDest().equals(v)) &&
						(e.getSources().get(0).equals(vertexThatHasChanged) || e.getSources().get(1).equals(vertexThatHasChanged) || e.getDest().equals(vertexThatHasChanged))	) {
							return handle (e);
					}
				}
				else {
					if ((e.getSource().equals(v) && e.getDest().equals(vertexThatHasChanged)) ||
						(e.getSource().equals(vertexThatHasChanged) && e.getDest().equals(v))) {
						return handle (e);
					}
				}
			}
		}
		return true;
	}
	
	private static boolean handleEdgeStartsWith (EdgeStartsWith e) {
		/*println ("[handleEdgeStartsWith] entered: " + e.toString());
		//println ("[handleEdgeStartsWith] " + e.getSource().getName() + " and " + e.getDest().getName());
		boolean a1Changed, a2Changed;
		a1Changed = false; a2Changed = false;
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		Automaton a2dotStart = mapAutomaton.get(e.getDest()).concatenate(AutomatonExtra.makeAnyStringFixed());
		//println ("[handleEdgeStartsWith] a1 example: '" + a1.getShortestExample(true) + "'");
		//println ("[handleEdgeStartsWith] a2 example: '" + a2.getShortestExample(true) + "'");
		
		Automaton intersection = AutomatonExtra.intersection(a1, a2dotStart);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeStartsWith] 1. intersection empty");
			elimanateCurrentLengths();
			return false;
		}
		
		if (!a1.equals(intersection)) {a1Changed = true;}
		mapAutomaton.put(e.getSource(), intersection);
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
		
		Automaton temp = AutomatonExtra.startingSubstrings(intersection);
		Automaton intersection2 = AutomatonExtra.intersection(temp, a2dotStart);
		//println ("[handleEdgeStartsWith] temp example: '" + temp.getFiniteStrings() + "'");
		//println ("[handleEdgeStartsWith] intersection2 example: '" + intersection2.getFiniteStrings() + "'");
		if (!a2.equals(intersection2)) {a2Changed = true;}
		mapAutomaton.put(e.getDest(), intersection2);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
		
		boolean result1, result2;
		result1 = true; result2 = true;
		if (a1Changed) {result1 = propagateChange(e.getSource(), e.getDest());}
		if (a2Changed) {result2 = propagateChange(e.getDest(), e.getSource());}
		return result1 && result2;
		*/
		//println ("[handleEdgeStartsWith] entered: " + e.toString());
		Automaton source = mapAutomaton.get(e.getSource());
		Automaton dest = mapAutomaton.get(e.getDest());
		
		boolean sourceChanged = false, destChanged = false;
		
		Automaton newSource = AutomatonExtra.intersection(source, dest.concatenate(AutomatonExtra.makeAnyStringFixed()));
		if (newSource.isEmpty()) {
			//println ("[handleEdgeStartsWith] newSource.isEmpty()");
			elimanateCurrentLengths();
			return false;
		}
		if (!newSource.equals(source)) {sourceChanged = true;}
		mapAutomaton.put(e.getSource(), newSource);
		if (!e.getSource().isConstant()) e.getSource().setSolution(newSource.getShortestExample(true));
		
		Automaton newDest = AutomatonExtra.intersection(dest, AutomatonExtra.startingSubstrings(source));
		if (newDest.isEmpty()) {
			//println ("[handleEdgeStartsWith] newDest.isEmpty()");
			elimanateCurrentLengths();
			return false;
		}
		if (!newDest.equals(dest)) {destChanged = true;}
		mapAutomaton.put(e.getDest(), newDest);
		if (!e.getDest().isConstant()) e.getDest().setSolution(newDest.getShortestExample(true));
		
		
		boolean result1, result2;
		result1 = true; result2 = true;
		if (sourceChanged) {result1 = propagateChange(e.getSource(), e.getDest());}
		if (destChanged) {result2 = propagateChange(e.getDest(), e.getSource());}
		return result1 && result2;
	}
	
	private static boolean handleEdgeNotStartsWith (EdgeNotStartsWith e) {
		//println ("[handleEdgeNotStartsWith] entered, doing nothing");
		/*boolean a1Changed = false;
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest()).concatenate(AutomatonExtra.makeAnyStringFixed());
		Automaton intersection = AutomatonExtra.intersection(a1, a2);
		Automaton newA = AutomatonExtra.intersection(a1, intersection.complement().intersection(AutomatonExtra.makeAnyStringFixed()));
		if (newA.isEmpty()) {
			//println ("[handleEdgeNotStartsWith] intersection empty");
			return false;
		}
		if (!a1.equals(newA)) {a1Changed = true;}
		mapAutomaton.put(e.getSource(), newA);
		if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
		if (a1Changed) {return propagateChange(e.getSource(), e.getDest());}*/
		
		//Do this lazily
		return true;
	}
	
	private static boolean handleEdgeEndsWith (EdgeEndsWith e) {
		/*println ("[handleEdgeEndsWith] entered: " + e.toString());
		boolean a1Changed, a2Changed;
		a1Changed = false; a2Changed = false;
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		Automaton dotStara2 = AutomatonExtra.makeAnyStringFixed().concatenate(mapAutomaton.get(e.getDest()));
		Automaton intersection = AutomatonExtra.intersection(a1, a2);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeEndsWith] 1. intersection empty");
			elimanateCurrentLengths();
			return false;
		}
		//println ("[handleEdgeEndsWith] intersection example: '" + intersection.getShortestExample(true) + "'");
		//println ("[handleEdgeEndsWith] source example: '" + a1.getShortestExample(true) + "'");
		//println ("[handleEdgeEndsWith] subtract1 example: '" + a1.complement().intersection(intersection).getShortestExample(true) + "'");
		//println ("[handleEdgeEndsWith] subtract2 example: '" + intersection.complement().intersection(a1).getShortestExample(true) + "'");
		if (!a1.equals(intersection)) {a1Changed = true;}
		//println ("[handleEdgeEndsWith] 1 done");
		mapAutomaton.put(e.getSource(), intersection);
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
		
		//println ("[handleEdgeEndsWith] 2"); 
		
		Automaton temp = AutomatonExtra.endingSubstrings(intersection);
		Automaton intersection2 = AutomatonExtra.intersection(temp, dotStara2);
		//println ("[handleEdgeEndsWith] 3");
		if (!a2.equals(intersection2)) {a2Changed = true;} //I think this was very slow
		//println ("[handleEdgeEndsWith] 3 done");
		mapAutomaton.put(e.getDest(), intersection2);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
		
		//println ("[handleEdgeEndsWith] 4"); 
		
		boolean result1, result2;
		result1 = true; result2 = true;
		if (a1Changed) {result1 = propagateChange(e.getSource(), e.getDest());}
		if (a2Changed) {result2 = propagateChange(e.getDest(), e.getSource());}
		return result1 && result2;*/
		//println ("[handleEdgeEndsWith] entered: " + e.toString());
		Automaton source = mapAutomaton.get(e.getSource());
		Automaton dest = mapAutomaton.get(e.getDest());
		
		boolean sourceChanged = false, destChanged = false;
		
		Automaton newSource = AutomatonExtra.intersection(source, AutomatonExtra.makeAnyStringFixed().concatenate(dest));
		if (newSource.isEmpty()) {
			elimanateCurrentLengths();
			return false;
		}
		if (!newSource.equals(source)) {sourceChanged = true;}
		mapAutomaton.put(e.getSource(), newSource);
		if (!e.getSource().isConstant()) e.getSource().setSolution(newSource.getShortestExample(true));
		
		Automaton newDest = AutomatonExtra.intersection(dest, AutomatonExtra.endingSubstrings(source));
		if (newDest.isEmpty()) {
			elimanateCurrentLengths();
			return false;
		}
		if (!newDest.equals(dest)) {destChanged = true;}
		mapAutomaton.put(e.getDest(), newDest);
		if (!e.getDest().isConstant()) e.getDest().setSolution(newDest.getShortestExample(true));
		
		
		boolean result1, result2;
		result1 = true; result2 = true;
		if (sourceChanged) {result1 = propagateChange(e.getSource(), e.getDest());}
		if (destChanged) {result2 = propagateChange(e.getDest(), e.getSource());}
		return result1 && result2;
	}
	
	private static boolean handleEdgeNotEndsWith (EdgeNotEndsWith e) {
		//println ("[handleEdgeNotEndsWith] entered");
		/*boolean a1Changed = false;
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = AutomatonExtra.makeAnyStringFixed().concatenate(mapAutomaton.get(e.getDest()));
		Automaton intersection = AutomatonExtra.intersection(a1, a2);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeNotEndsWith] intersection empty");
			return false;
		}
		Automaton newA = AutomatonExtra.intersection(a1, intersection.complement().intersection(AutomatonExtra.makeAnyStringFixed()));
		if (!a1.equals(newA)) a1Changed = true;
		mapAutomaton.put(e.getSource(), newA);
		if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
		if (a1Changed) {return propagateChange(e.getSource(), e.getDest());}*/
		
		//Do this lazily
		
		return true;
	}
	
	private static boolean handleEdgeCharAt (EdgeCharAt e) {
		//println ("[handleEdgeCharAt] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = Automaton.makeChar((char) e.getValue().solution());
		Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
		Automaton intersection = AutomatonExtra.intersection(a1, temp);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeCharAt] 1. intersection empty, making index == -1 because the character could not be found anywhere");
			//Done: Test performance, looks good
			LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant (e.getIndex().solution())));
			loic.addToList(new LinearIntegerConstraint(e.getValue(), Comparator.NE, new IntegerConstant (e.getValue().solution())));				
			global_pc._addDet(loic);			

			return false;
		}
		else {
			temp = AutomatonExtra.lengthAutomaton(e.getIndex().solutionInt());
			temp = temp.concatenate(Automaton.makeChar((char) e.getValue().solution()).concatenate(AutomatonExtra.makeAnyStringFixed()));
			intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeCharAt] 2. intersection empty, current index or value is not valid");
				LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant (e.getIndex().solution())));
				loic.addToList(new LinearIntegerConstraint(e.getValue(), Comparator.NE, new IntegerConstant (e.getValue().solution())));				
				global_pc._addDet(loic);
				return false;
			}
			else {
				boolean a1Changed = false;
				if (!intersection.equals(a1)) a1Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (a1Changed) {return propagateChange(e.getSource(), e.getDest());}
			}
		}
		return true;
	}
	
	private static boolean handleEdgeReplaceCharChar (EdgeReplaceCharChar e) {
		//println ("[handleEdgeReplaceCharChar] doing it");
		Automaton source = mapAutomaton.get(e.getSource());
		Automaton dest = mapAutomaton.get(e.getDest());
		
		boolean sourceChanged = false, destChanged = false;
		Automaton replacedAutomaton = new Replace1(e.getC1(), e.getC2()).op(dest);
		//println ("[handleEdgeReplaceCharChar] replacedAutomaton: " + replacedAutomaton.getFiniteStrings(2));
		Automaton newDest = dest.intersection(replacedAutomaton);
		//println ("[handleEdgeReplaceCharChar] dest: " + dest.getFiniteStrings(2));
		if (newDest.isEmpty()) {
			//println ("[handleEdgeReplaceCharChar] newDest.isEmpty()");
			elimanateCurrentLengths();
			//throw new RuntimeException ("return false");
			return false;
		}
		if (!newDest.equals(dest)) {destChanged = true;
			//println ("[handleEdgeReplaceCharChar] destChanged");
		}
		mapAutomaton.put(e.getDest(), newDest);
		if (!e.getDest().isConstant()) e.getDest().setSolution(newDest.getShortestExample(true));
		
		Automaton newSource = source.intersection(AutomatonExtra.reverseReplace(dest, e.getC1()));
		if (newSource.isEmpty()) {
			//println ("[handleEdgeReplaceCharChar] newSource.isEmpty()");
			elimanateCurrentLengths();
			return false;
		}
		if (!newSource.equals(source)) {sourceChanged = true;
			//println ("[handleEdgeReplaceCharChar] sourceChanged");
		}
		mapAutomaton.put(e.getSource(), newSource);
		if (!e.getSource().isConstant()) e.getSource().setSolution(newSource.getShortestExample(true));
		
		boolean result;
		result = true;
		//println ("[handleEdgeReplaceCharChar] " + sourceChanged + " " + destChanged);
		if (sourceChanged) {result = propagateChange(e.getSource(), e.getDest());}
		if (destChanged) {result = result & propagateChange(e.getDest(), e.getSource());}
		return result;
	}
	
	private static boolean handleEdgeConcat (EdgeConcat e) {
		//println ("[handleEdgeConcat] entered");
		
		//Backward solving of this needs to be done lazily
		
		Automaton a1 = mapAutomaton.get(e.getSources().get(0));
		Automaton a2 = mapAutomaton.get(e.getSources().get(1));
		Automaton a3 = mapAutomaton.get(e.getDest());
		
		boolean a3changed = false;
		Automaton concatA = a1.concatenate(a2);
		Automaton intersection = AutomatonExtra.intersection(concatA, a3);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeConcat] intersection is empty");
			elimanateCurrentLengths();
			return false;
		}
		if (!a3.equals(intersection)) a3changed = true;
		mapAutomaton.put(e.getDest(), intersection);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection.getShortestExample(true));
		
		boolean a1changed = false;
		Automaton temp = AutomatonExtra.substring(intersection, 0, e.getSources().get(0).getLength());
		Automaton intersection2 = AutomatonExtra.intersection(a1, temp);
		if (intersection2.isEmpty()) {
			//println ("[handleEdgeConcat] intersection2 is empty");
			elimanateCurrentLengths();
			return false;
		}

		if (!a1.equals(intersection2)) a1changed = true;
		mapAutomaton.put(e.getSources().get(0), intersection2);
		if (!e.getSources().get(0).isConstant()) e.getSources().get(0).setSolution(intersection2.getShortestExample(true));
		
		boolean a2changed = false;
		temp = AutomatonExtra.substring(intersection, e.getSources().get(0).getLength());
		Automaton intersection3 = AutomatonExtra.intersection(a2, temp);
		if (intersection3.isEmpty()) {
			//println ("[handleEdgeConcat] intersection3 is empty");
			elimanateCurrentLengths();
			return false;
		}

		if (!a2.equals(intersection3)) a2changed = true;
		mapAutomaton.put(e.getSources().get(1), intersection3);
		if (!e.getSources().get(1).isConstant()) e.getSources().get(1).setSolution(intersection3.getShortestExample(true));
		
		boolean propResult = true;
		if (a3changed) {propResult = propResult && propagateChange(e.getDest(), e.getSources().get(0));}
		if (a1changed) {propResult = propResult && propagateChange(e.getSources().get(0), e.getDest());}
		if (a2changed) {propResult = propResult && propagateChange(e.getSources().get(1), e.getDest());}
		return propResult;
		
	}
	
	private static boolean handleEdgeContains (EdgeContains e) {
		//println ("[handleEdgeContains] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		
		Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
		Automaton intersection = AutomatonExtra.intersection(a1, temp);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeContains] intersection empty");
			elimanateCurrentLengths();
			return false;
		}
		boolean a1Changed = false;
		if (!a1.equals(intersection)) {a1Changed = true;
			//println ("[handleEdgeContains] a1Changed");
		}
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
		mapAutomaton.put(e.getSource(), intersection);
		
		Automaton subsets = new Substring().op(a1);
		intersection = AutomatonExtra.intersection(a2, subsets);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeContains] intersection empty");
			elimanateCurrentLengths();
			return false;
		}
		boolean a2Changed = false;
		if (!a2.equals(intersection)) {a2Changed = true;
			//println ("[handleEdgeContains] a2Changed");
		}
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection.getShortestExample(true));
		mapAutomaton.put(e.getDest(), intersection);
		
		boolean propResult = true;
		if (a1Changed) propResult = propagateChange(e.getSource(), e.getDest());
		if (a2Changed) propResult = propResult & propagateChange(e.getDest(), e.getSource());
		return propResult;
	}
	
	private static boolean handleEdgeIndexOf (EdgeIndexOf e) {
		//println ("[handleEdgeIndexOf] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		//println (String.format("[handleEdgeIndexOf] a1: '%s'", a1.getShortestExample(true)));
		Automaton a2 = mapAutomaton.get(e.getDest());
		//println (String.format("[handleEdgeIndexOf] a2: '%s'", a2.getShortestExample(true)));
		int index = e.getIndex().solutionInt();
		//First check if it is possible
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] indexof could not be found anywhere, forcing index == -1 or longer length for " + e.getSource().getName());
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				//global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				global_pc._addDet(loic);
				return false;
			}
			//Make sure the destination is not present in source before index.
			//println ("[handlEdgeIndexOf: " + index);
			Automaton exclude = Automaton.makeEmpty();
			for (int i = 0; i <= index - e.getDest().getLength(); i++) {
				Automaton prefixSpaces = AutomatonExtra.lengthAutomaton(i);
				Automaton suffixSpaces = AutomatonExtra.lengthAutomaton(index - i - e.getDest().getLength());
				Automaton aNew = prefixSpaces.concatenate(a2).concatenate(suffixSpaces);
				//println (String.format("[handleEdgeIndexOf] aNew: '%s'", aNew.getShortestExample(true)));
				exclude = exclude.union(aNew);
			}
			//println (String.format("[handleEdgeIndexOf] exclude: '%s'", exclude.getShortestExample(true)));
			//Lengthen exclude
			Automaton lengthenExclude = exclude.concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton excludeInverse = lengthenExclude.complement().intersection(AutomatonExtra.makeAnyStringFixed());
			excludeInverse = AutomatonExtra.intersection(excludeInverse, AutomatonExtra.lengthAutomaton(e.getSource().getLength()));
			//println (String.format("[handleEdgeIndexOf] excludeInverser: '%s'", excludeInverse.getShortestExample(true)));
			//println (String.format("a1: '%s'", a1.getShortestExample(true)));
			a1 = AutomatonExtra.intersection(a1, excludeInverse);
			if (a1.isEmpty()) {
				//println ("[handleEdgeIndexOf] String encountered before");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(index))); //TODO: Must be equal to -1?
				//global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				global_pc._addDet(loic);
				return false;
			}
			//println ("[handleEdgeIndexOf] not empty");
			mapAutomaton.put(e.getSource(), a1);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
			//println(String.format("a1 example: '%s'", a1.getShortestExample(true)));
			
			
			//Remove source.substring(0, dest.length) from dest
			/*exclude = AutomatonExtra.substring(a1, 0, e.getDest().getLength());
			if (exclude.getShortestExample(true).length() != e.getDest().getLength()) {
				throw new RuntimeException("assumption fail");
			}
			//println(String.format("exclude example: '%s'", exclude.getShortestExample(true)));
			excludeInverse = exclude.complement().intersection(AutomatonExtra.makeAnyStringFixed());
			//println(String.format("excludeInverse example: '%s'", excludeInverse.getShortestExample(true)));
			excludeInverse = AutomatonExtra.intersection(excludeInverse, AutomatonExtra.lengthAutomaton(e.getDest().getLength()));
			//println(String.format("excludeInverse example: '%s'", excludeInverse.getShortestExample(true)));
			//println(String.format("a2 example: '%s'", a2.getShortestExample(true)));
			a2 = AutomatonExtra.intersection(a2, excludeInverse);
			//println(String.format("a2 example: '%s'", a2.getShortestExample(true)));
			mapAutomaton.put(e.getDest(), a2);
			if (!e.getDest().isConstant()) e.getDest().setSolution(a2.getShortestExample(true));*/
			
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			//println ("[handleEdgeIndexOf] intersection example: " + intersection.getShortestExample(true));
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] 1. indexof could not be applyied at the current place");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				//global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				global_pc._addDet(loic);
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
					//println ("[handleEdgeIndexOf] 2. indexof could not be applyied at the current place");
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
					return false;
				}
				if (!a2.equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				boolean propResult = true;
				if (a1Changed) propResult = propagateChange(e.getSource(), e.getDest());
				if (a2Changed) propResult = propResult && propagateChange(e.getDest(), e.getSource());
				return propResult;
			}
		}
		else {
			/*Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.minus(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a1Changed = false;
			if (!a1.equals(intersection)) a1Changed = true;
			mapAutomaton.put(e.getSource(), a1);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
			
			temp = new Substring().op(a1);
			Automaton intersection2 = AutomatonExtra.minus(a2, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a2Changed = false;
			if (!a2.equals(intersection2)) a2Changed = true;
			mapAutomaton.put(e.getDest(), a2);
			if (!e.getDest().isConstant()) e.getDest().setSolution(a2.getShortestExample(true));
			
			boolean propResult = true;
			if (a1Changed) {propResult = propResult && propagateChange(e.getSource(), e.getDest());}
			if (a2Changed) {propResult = propResult && propagateChange(e.getDest(), e.getSource());}
			return propResult;*/
			
			//handle in handleNots
			return true;
		}
		//return true;
	}
	
	//TODO: Finish properly
	private static boolean handleEdgeLastIndexOf (EdgeLastIndexOf e) {
		//println ("[handleEdgeIndexOf] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		//First check if it is possible
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] indexof could not be found anywhere, forcing index == -1 or longer length for " + e.getSource().getName());
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				//global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				global_pc._addDet(loic);
				return false;
			}
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			//println ("[handleEdgeIndexOf] intersection example: " + intersection.getShortestExample(true));
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] 1. indexof could not be applyied at the current place");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				//global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				global_pc._addDet(loic);
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
					//println ("[handleEdgeIndexOf] 2. indexof could not be applyied at the current place");
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
					return false;
				}
				if (!a2.equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				boolean propResult = true;
				if (a1Changed) propResult = propagateChange(e.getSource(), e.getDest());
				if (a2Changed) propResult = propResult && propagateChange(e.getDest(), e.getSource());
				return propResult;
			}
		}
		else {
			/*Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.minus(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a1Changed = false;
			if (!a1.equals(intersection)) a1Changed = true;
			mapAutomaton.put(e.getSource(), a1);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
			
			temp = new Substring().op(a1);
			Automaton intersection2 = AutomatonExtra.minus(a2, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a2Changed = false;
			if (!a2.equals(intersection2)) a2Changed = true;
			mapAutomaton.put(e.getDest(), a2);
			if (!e.getDest().isConstant()) e.getDest().setSolution(a2.getShortestExample(true));
			
			boolean propResult = true;
			if (a1Changed) {propResult = propResult && propagateChange(e.getSource(), e.getDest());}
			if (a2Changed) {propResult = propResult && propagateChange(e.getDest(), e.getSource());}
			return propResult;*/
			
			//handle in handleNots
			return true;
		}
		//return true;
	}
	
	private static boolean handleEdgeIndexOf2 (EdgeIndexOf2 e) {
		//println ("[handleEdgeIndexOf2] entered: " + e.getName());
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		//First check if it is possible
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] indexof could not be found anywhere, forcing index == -1 or longer length for " + e.getSource().getName());
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				//global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				global_pc._addDet(loic);
				return false;
			}
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			//println ("[handleEdgeIndexOf] intersection example: " + intersection.getShortestExample(true));
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] 1. indexof could not be applyied at the current place");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				//global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				global_pc._addDet(loic);
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
					//println ("[handleEdgeIndexOf] 2. indexof could not be applyied at the current place");
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
					return false;
				}
				if (!a2.equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				boolean propResult = true;
				if (a1Changed) propResult = propagateChange(e.getSource(), e.getDest());
				if (a2Changed) propResult = propResult && propagateChange(e.getDest(), e.getSource());
				return propResult;
			}
		}
		else {
			/*Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.minus(a1, temp);
			//println ("[handleEdgeIndexOf2] temp example: '" + temp.getShortestExample(true) + "'");
			//println ("[handleEdgeIndexOf2] intersection example: '" + intersection.getShortestExample(true) + "'");
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf2] 1. indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a1Changed = false;
			//println ("[handleEdgeIndexOf2]\n" + a1.toDot() +"\n" + intersection.toDot());
			if (!a1.equals(intersection)) a1Changed = true;
			mapAutomaton.put(e.getSource(), intersection);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
			
			temp = new Substring().op(a1);
			Automaton intersection2 = AutomatonExtra.minus(a2, temp);
			if (intersection2.isEmpty()) {
				//println ("[handleEdgeIndexOf2] 2. indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a2Changed = false;
			if (!a2.equals(intersection2)) a2Changed = true;
			mapAutomaton.put(e.getDest(), intersection2);
			if (!e.getDest().isConstant()) e.getDest().setSolution(a2.getShortestExample(true));
			
			boolean propResult = true;
			if (a1Changed) {propResult = propResult && propagateChange(e.getSource(), e.getDest());}
			if (a2Changed) {propResult = propResult && propagateChange(e.getDest(), e.getSource());}
			return propResult;*/
			
			//handle in handleNots
			return true;
		}
		//return true;
	}
	
	private static boolean handleEdgeIndexOfChar (EdgeIndexOfChar e) {
		//println ("[handleEdgeIndexOfChar] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		//Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		String character = String.valueOf((char) e.getIndex().getExpression().solution());
		//First check if it is possible
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			//println ("[handleEdgeIndexOfChar] temp example: '" + temp.getShortestExample(true) + "'");
			//println ("[handleEdgeIndexOfChar] a1 example: '" + a1.getShortestExample(true) + "'");
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOfChar] 1. indexof '" + character + "' could not be found anywhere, forcing index == -1 or longer lengths");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				//global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				global_pc._addDet(loic);
				//println ("[handleEdgeIndexOfChar] " + global_pc.toString());
				return false;
			}
			
			//Make sure the destination is not present in source before index.
			//println ("[handlEdgeIndexOf: " + index);
			Automaton exclude = Automaton.makeEmpty();
			for (int i = 0; i <= index - e.getDest().getLength(); i++) {
				Automaton prefixSpaces = AutomatonExtra.lengthAutomaton(i);
				Automaton suffixSpaces = AutomatonExtra.lengthAutomaton(index - i - e.getDest().getLength());
				Automaton aNew = prefixSpaces.concatenate(Automaton.makeChar(character.charAt(0))).concatenate(suffixSpaces);
				//println (String.format("[handleEdgeIndexOf] aNew: '%s'", aNew.getShortestExample(true)));
				exclude = exclude.union(aNew);
			}
			//println (String.format("[handleEdgeIndexOf] exclude: '%s'", exclude.getShortestExample(true)));
			//Lengthen exclude
			Automaton lengthenExclude = exclude.concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton excludeInverse = lengthenExclude.complement().intersection(AutomatonExtra.makeAnyStringFixed());
			excludeInverse = AutomatonExtra.intersection(excludeInverse, AutomatonExtra.lengthAutomaton(e.getSource().getLength()));
			//println (String.format("[handleEdgeIndexOf] excludeInverser: '%s'", excludeInverse.getShortestExample(true)));
			//println (String.format("a1: '%s'", a1.getShortestExample(true)));
			a1 = AutomatonExtra.intersection(a1, excludeInverse);
			if (a1.isEmpty()) {
				//println ("[handleEdgeIndexOf] String encountered before");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(index))); //TODO: Must be equal to -1?
				//global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				global_pc._addDet(loic);
				return false;
			}
			//println ("[handleEdgeIndexOf] not empty");
			mapAutomaton.put(e.getSource(), a1);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
			
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			//println ("[handleEdgeIndexOf] intersection example: " + intersection.getShortestExample(true));
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOfChar] 2. indexof at " + index + " could not be applyied at the current place ('" + e.getSource().getSolution() + "', '" + e.getDest().getSolution()+ "')");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				//global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				global_pc._addDet(loic);
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
					//println ("[handleEdgeIndexOf] 3. indexof could not be applyied at the current place");
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
					return false;
				}
				if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				boolean propResult = true;
				if (a1Changed) propResult = propagateChange(e.getSource(), e.getDest());
				if (a2Changed) propResult = propResult && propagateChange(e.getDest(), e.getSource());
				return propResult;
			}
		}
		else {
			/*Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.minus(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a1Changed = false;
			if (!a1.equals(intersection)) a1Changed = true;
			mapAutomaton.put(e.getSource(), a1);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
			
			temp = new Substring().op(a1);
			Automaton intersection2 = AutomatonExtra.minus(Automaton.makeString(character), temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a2Changed = false;
			if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
			mapAutomaton.put(e.getDest(), Automaton.makeString(character));
			if (!e.getDest().isConstant()) e.getDest().setSolution(Automaton.makeString(character).getShortestExample(true));
			
			boolean propResult = true;
			if (a1Changed) {propResult = propResult && propagateChange(e.getSource(), e.getDest());}
			if (a2Changed) {propResult = propResult && propagateChange(e.getDest(), e.getSource());}
			return propResult;*/
			
			//handle in handleNots
			return true;
		}
		//return true;
	}
	
	private static boolean handleEdgeLastIndexOfChar (EdgeLastIndexOfChar e) {
		//println ("[handleEdgeLastIndexOfChar] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		//Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		String character = String.valueOf((char) e.getIndex().getExpression().solution());
		//First check if it is possible
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeLastIndexOfChar] 1.indexof could not be found anywhere, forcing index == -1 or longer length for " + e.getSource().getName());
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				//global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				global_pc._addDet(loic);
				//println ("[handleEdgeLastIndexOfChar] " + global_pc.toString());
				
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
				//println ("[handleEdgeLastIndexOfChar] 2. indexof could not be applyied at the current place");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				//global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				global_pc._addDet(loic);
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
					//println ("[handleEdgeLastIndexOfChar] 3. indexof could not be applyied at the current place");
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
					return false;
				}
				if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				boolean propResult = true;
				if (a1Changed) propResult = propagateChange(e.getSource(), e.getDest());
				if (a2Changed) propResult = propResult && propagateChange(e.getDest(), e.getSource());
				return propResult;
			}
		}
		else {
			
			//handle in handleNots
			//println ("[handleEdgeLastIndexOfChar] handle in handleNots");
			return true;
		}
		//return true;
	}
	
	private static boolean handleEdgeLastIndexOfChar2 (EdgeLastIndexOfChar2 e) {
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
				//println ("[handleEdgeLastIndexOfChar] 1.indexof could not be found anywhere, forcing index == -1 or longer length for " + e.getSource().getName());
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				//global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				global_pc._addDet(loic);
				//println ("[handleEdgeLastIndexOfChar] " + global_pc.toString());
				
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
				//println ("[handleEdgeLastIndexOfChar] 2. indexof could not be applyied at the current place");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				loic.addToList(new LinearIntegerConstraint(e.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(e.getIndex().getMinDist().solution())));
				//global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				global_pc._addDet(loic);
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
					//println ("[handleEdgeLastIndexOfChar] 3. indexof could not be applyied at the current place");
					//global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
					LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
					loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
					loic.addToList(new LinearIntegerConstraint(e.getIndex().getMinDist(), Comparator.NE, new IntegerConstant(e.getIndex().getMinDist().solution())));
					global_pc._addDet(loic);
					return false;
				}
				if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				boolean propResult = true;
				if (a1Changed) propResult = propagateChange(e.getSource(), e.getDest());
				if (a2Changed) propResult = propResult && propagateChange(e.getDest(), e.getSource());
				return propResult;
			}
		}
		else {
			
			//handle in handleNots
			return true;
		}
		//return true;
	}
	
	private static boolean handleEdgeIndexOfChar2 (EdgeIndexOfChar2 e) {
		//println ("[handleEdgeIndexOfChar2] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		//Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		String character = String.valueOf((char) e.getIndex().getExpression().solution());
		//First check if it is possible
		if (index > -1) {
			//println ("[handleEdgeIndexOfChar2] index > -1");
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			Automaton intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOfChar2] indexof could not be found anywhere, forcing index == -1 or longer length for " + e.getSource().getName());
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				//global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				global_pc._addDet(loic);
				return false;
			}
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			//println ("[handleEdgeIndexOf] intersection example: " + intersection.getShortestExample(true));
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOfChar2] 1. indexof could not be applyied at the current place");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				//global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				global_pc._addDet(loic);
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
					//println ("[handleEdgeIndexOfChar2] 2. indexof could not be applyied at the current place");
					global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
					return false;
				}
				if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
				mapAutomaton.put(e.getSource(), intersection);
				mapAutomaton.put(e.getDest(), intersection2);
				if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
				if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
				boolean propResult = true;
				if (a1Changed) propResult = propagateChange(e.getSource(), e.getDest());
				if (a2Changed) propResult = propResult && propagateChange(e.getDest(), e.getSource());
				return propResult;
			}
		}
		else {
			//println ("[handleEdgeIndexOfChar2] index == -1");
			/*Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
			//println ("[handleEdgeIndexOfChar2] temp example: '" + temp.getShortestExample(true) + "'");
			//println ("[handleEdgeIndexOfChar2] a1 example: '" + a1.getShortestExample(true) + "'");
			Automaton intersection = AutomatonExtra.minus(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOfChar2] 1. indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a1Changed = false;
			//println ("[handleEdgeIndexOfChar2]\n" + a1.toDot() +"\n" + intersection.toDot());
			if (!a1.equals(intersection)) a1Changed = true;
			mapAutomaton.put(e.getSource(), intersection);
			if (!e.getSource().isConstant()) e.getSource().setSolution(a1.getShortestExample(true));
			
			temp = new Substring().op(a1);
			Automaton intersection2 = AutomatonExtra.minus(Automaton.makeString(character), temp);
			if (intersection2.isEmpty()) {
				//println ("[handleEdgeIndexOfChar2] 2. indexof == -1 could not be enforced");
				global_pc._addDet (Comparator.GT, e.getIndex(), -1);
				return false;
			}
			boolean a2Changed = false;
			if (!Automaton.makeString(character).equals(intersection2)) a2Changed = true;
			mapAutomaton.put(e.getDest(), intersection2);
			if (!e.getDest().isConstant()) e.getDest().setSolution(Automaton.makeString(character).getShortestExample(true));
			
			boolean propResult = true;
			if (a1Changed) {propResult = propResult && propagateChange(e.getSource(), e.getDest());}
			if (a2Changed) {propResult = propResult && propagateChange(e.getDest(), e.getSource());}
			return propResult;*/
			
			//handle in handleNots
			return true;
		}
		//return true;
	}

	
	private static boolean handleEdgeNotContains (EdgeNotContains e) {
		//println ("[handleEdgeNotContains] entered");
		//Should be done lazily, because its equivalent to unequality
		
		return true;
	}
	
	private static boolean handleEdgeSubstring1Equal (EdgeSubstring1Equal e) {
		//println ("[handleEdgeSubstring1Equal] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		
		Automaton temp = AutomatonExtra.substring(a1, e.getArgument1());
		//println ("[handleEdgeSubstring1Equal] substring example: '" + temp.getShortestExample(true) + "'");
		Automaton intersection = AutomatonExtra.intersection(temp, a2);
		//println ("[handleEdgeSubstring1Equal] intersection example: '" + intersection.getShortestExample(true) + "'");
		//println ("[handleEdgeSubstring1Equal] intersection example: '" + intersection.getStrings(1) + "'");
		if (intersection.isEmpty()) {
			//println ("[handleEdgeSubstring1Equal] intersection empty");
			elimanateCurrentLengths();
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
			//println ("[handleEdgeSubstring1Equal] intersection empty");
			LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
			loic.addToList(new LinearIntegerConstraint(e.getArgument1Symbolic(), Comparator.NE, new IntegerConstant(e.getArgument1Symbolic().solution())));
			global_pc._addDet(loic);
			return false;
		}
		boolean a1Changed = false;
		if (!a1.equals(intersection2)) a1Changed = true;
		mapAutomaton.put(e.getSource(), intersection2);
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection2.getShortestExample(true));
		
		boolean propResult = true;
		if (a2Changed) {propResult = propagateChange(e.getDest(), e.getSource());}
		if (a1Changed) {propResult = propResult && propagateChange(e.getSource(), e.getDest());}
		
		return propResult;
	}
	
	private static boolean handleEdgeSubstring2Equal (EdgeSubstring2Equal e) {
		//println ("[handleEdgeSubstring2Equal] entered " + e);
		Automaton source = mapAutomaton.get(e.getSource());
		Automaton dest = mapAutomaton.get(e.getDest());
		if (!e.hasSymbolicArgs()) {
			
			Automaton temp = AutomatonExtra.substring(source, e.getArgument1(), e.getArgument2());
			Automaton intersection = AutomatonExtra.intersection(temp, dest);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeSubstring2Equal] 1. intersection empty");
				elimanateCurrentLengths();
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
				//println ("[handleEdgeSubstring2Equal] 2. intersection empty");
				elimanateCurrentLengths();
				return false;
			}
			boolean a1Changed = false;
			if (!source.equals(intersection2)) a1Changed = true;
			mapAutomaton.put(e.getSource(), intersection2);
			if (!e.getSource().isConstant()) e.getSource().setSolution(intersection2.getShortestExample(true));
			
			boolean propResult = true;
			if (a2Changed) {propResult = propagateChange(e.getDest(), e.getSource());}
			if (a1Changed) {propResult = propResult && propagateChange(e.getSource(), e.getDest());}
			
			return propResult;
		}
		else if (e.getSymbolicArgument2() != null && e.getSymbolicArgument1() == null) {
			int arg2 = e.getSymbolicArgument2().solutionInt();
			Automaton temp = AutomatonExtra.substring(source, e.getArgument1(), arg2);
			//println ("[handleEdgeSubstring2Equal] source.getLength() = " + e.getSource().getLength());
			//println ("[handleEdgeSubstring2Equal] temp diff = " + (arg2 - e.getArgument1()));
			Automaton intersection = AutomatonExtra.intersection(temp, dest);
			
			if (intersection.isEmpty()) {
				//println ("[handleEdgeSubstring2Equal] 3. intersection empty");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(arg2)));
				global_pc._addDet(loic);
				//println ("[handleEdgeSubstring2Equal] loic: " + loic);
				//throw new RuntimeException ();
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
				//println ("[handleEdgeSubstring2Equal] 4. intersection empty");
				LogicalORLinearIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				loic.addToList(new LinearIntegerConstraint(e.getSymbolicArgument2(), Comparator.NE, new IntegerConstant(arg2)));
				global_pc._addDet(loic);
				return false;
			}
			boolean a1Changed = false;
			if (!source.equals(intersection2)) a1Changed = true;
			mapAutomaton.put(e.getSource(), intersection2);
			if (!e.getSource().isConstant()) e.getSource().setSolution(intersection2.getShortestExample(true));
			
			boolean propResult = true;
			if (a2Changed) {propResult = propagateChange(e.getDest(), e.getSource());}
			if (a1Changed) {propResult = propResult && propagateChange(e.getSource(), e.getDest());}
			
			return propResult;
		}
		else {
			throw new RuntimeException ("Not supported, yet");
		}
	}
	
	private static boolean handleEdgeTrimEqual (EdgeTrimEqual e) {
		//println ("[handleEdgeTrimEqual] entered " + e.toString());
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		//println ("[handleEdgeTrimEqual] " + e.getSource().getName() + " and " + e.getDest().getName());
		//println ("[handleEdgeTrimEqual] a1 examples: '" + a1.getShortestExample(true) + "'");
		//println ("[handleEdgeTrimEqual] a2 examples: '" + a2.getShortestExample(true) + "'");
		
		
		Automaton temp = new Trim().op(a1);
		temp = AutomatonExtra.minus(temp, Automaton.makeEmptyString());
		//println ("[handleEdgeTrimEqual] trim examples: '" + temp.getShortestExample(true) + "'");
		Automaton intersection = AutomatonExtra.intersection(a2, temp);
		//println ("[handleEdgeTrimEqual] trim intersection: '" + intersection.getShortestExample(true) + "'");
		if (intersection.isEmpty()) {
			//println ("[handleEdgeTrimEqual] 1. intersection empty");
			elimanateCurrentLengths();
			return false;
		}
		boolean a2Changed = false;
		if (!a2.equals(intersection)) a2Changed = true;
		mapAutomaton.put (e.getDest(), intersection);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection.getShortestExample(true));
		
		Automaton temp2 = AutomatonExtra.star(Automaton.makeCharRange((char) 32, (char) 127)).concatenate(intersection).concatenate(AutomatonExtra.star(Automaton.makeCharRange((char) 32, (char) 127)));
		Automaton intersection2 = AutomatonExtra.intersection(a1, temp2);
		if (intersection2.isEmpty()) {			
			//println ("[handleEdgeTrimEqual] 2. intersection empty");
			elimanateCurrentLengths();
			return false;
		}
		boolean a1Changed = false;
		if (!a1.equals(intersection2)) a1Changed = true;
		mapAutomaton.put(e.getSource(), intersection2);
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection2.getShortestExample(true));
		
		boolean propResult = true;
		if (a2Changed) {propResult = propagateChange(e.getDest(), e.getSource());}
		if (a1Changed) {propResult = propResult && propagateChange(e.getSource(), e.getDest());}
		
		return propResult;
	}
	
	private static void elimanateCurrentLengths () {
		//println ("elimanateCurrentLengths");
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		int count = 0;
		for (Vertex v: global_graph.getVertices()) {
			if (v.isConstant()) continue;
			loic.addToList(new LinearIntegerConstraint(v.getSymbolicLength(), Comparator.NE, new IntegerConstant(v.getLength())));
			count++;
		}
		if (count == 1) {
			loic.addToList(new LinearIntegerConstraint(new IntegerConstant(1), Comparator.EQ, new IntegerConstant(0)));
		}
		global_pc._addDet(loic);
		//println (global_pc.toString());
	}
	
	private static LogicalORLinearIntegerConstraints elimanateCurrentLengthsConstraints() {
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		for (Vertex v: global_graph.getVertices()) {
			if (v.isConstant()) continue;
			if (v.getName().startsWith("CHAR")) continue;
			loic.addToList(new LinearIntegerConstraint(v.getSymbolicLength(), Comparator.NE, new IntegerConstant(v.getLength())));
		}
		return loic;
	}
	

}

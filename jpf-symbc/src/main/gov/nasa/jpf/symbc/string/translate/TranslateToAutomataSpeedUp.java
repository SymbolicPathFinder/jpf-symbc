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
import gov.nasa.jpf.symbc.string.graph.Edge;
import gov.nasa.jpf.symbc.string.graph.EdgeCharAt;
import gov.nasa.jpf.symbc.string.graph.EdgeConcat;
import gov.nasa.jpf.symbc.string.graph.EdgeContains;
import gov.nasa.jpf.symbc.string.graph.EdgeEndsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOf;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOf2;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOfChar;
import gov.nasa.jpf.symbc.string.graph.EdgeIndexOfChar2;
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

public class TranslateToAutomataSpeedUp {
	private static Map<Vertex, Integer> mapSolved;
	private static Map<Vertex, Automaton> mapAutomaton;
	private static Map<Vertex, Integer> mapEdgeCount;
	private static Map<EdgeConcat, Integer> mapConcat;
	
	private static StringGraph global_graph;
	private static PathCondition global_pc;
	
	private static int concatCount = 128;
	
	private static boolean logging = true;
	
	static SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
	/*
	 * The trim operation from JSA does not work with length of 1 characters!!
	 */
	public static boolean isSat (StringGraph g, PathCondition pc) {
		boolean restart = true;
		while (restart) {
			restart = false;
			global_graph = g;
			global_pc  = pc;
			mapSolved = new HashMap<Vertex, Integer>();
			mapAutomaton = new HashMap<Vertex, Automaton>();
			mapConcat = new HashMap<EdgeConcat, Integer>();
			for (Vertex v: g.getVertices()) {
				mapSolved.put(v, new Integer(0));
				Automaton length = AutomatonExtra.lengthAutomaton(v.getLength());
				if (!v.isConstant()) {
					mapAutomaton.put(v, AutomatonExtra.makeAnyStringFixed().intersection(length));
				}
				else {
					mapAutomaton.put(v, Automaton.makeString(v.getSolution()).intersection(length));
				}
			}
			
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
									//println ("[isSat] solving path condition: ");
									//println(global_pc.header.toString());
									if (scg.isSatisfiable(global_pc)) {
										scg.solve(global_pc);
										//println ("[isSat] solved");
										PathCondition.flagSolved = true;
										//println(global_pc.header.toString());
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
			}
			
			
			//At this point the entire graph should have been mostly solved
			
			//Take care of nonequality and concat
			boolean handleNotResult = handleNots(g);
			if (!handleNotResult) {
				if (PathCondition.flagSolved == false) {
					if (scg.isSatisfiable(global_pc)) {
						scg.solve(global_pc);
						PathCondition.flagSolved = true;
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
		return true;
	}
	
	private static boolean handleNots (StringGraph g) {
		int nonequalityFlipFlop = 0;
		boolean change = true;
		while (change) {
			change = false;
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
								if (temp.isEmpty()) return false;
								if (!enc.getSource().isConstant()) enc.getSource().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(enc.getSource(), temp);
								boolean propResult = propagateChange(enc.getSource(), enc.getDest());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
							else {
								Automaton a1 = mapAutomaton.get(enc.getDest());
								Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getDest().getSolution()));
								if (temp.isEmpty()) return false;
								if (!enc.getDest().isConstant()) enc.getDest().setSolution(temp.getShortestExample(true));
								mapAutomaton.put(enc.getDest(), temp);
								boolean propResult = propagateChange(enc.getDest(), enc.getSource());
								if (!propResult) return false;
								nonequalityFlipFlop = (nonequalityFlipFlop + 1) % 2;
							}
						}
						else if (!enc.getSource().isConstant()) {
							Automaton a1 = mapAutomaton.get(enc.getSource());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getSource().getSolution()));
							if (temp.isEmpty()) return false;
							if (!enc.getSource().isConstant()) enc.getSource().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(enc.getSource(), temp);
							boolean propResult = propagateChange(enc.getSource(), enc.getDest());
							if (!propResult) return false;
						}
						else if (!enc.getDest().isConstant()) {
							Automaton a1 = mapAutomaton.get(enc.getDest());
							Automaton temp = AutomatonExtra.minus (a1, Automaton.makeString(enc.getDest().getSolution()));
							if (temp.isEmpty()) return false;
							if (!enc.getDest().isConstant()) enc.getDest().setSolution(temp.getShortestExample(true));
							mapAutomaton.put(enc.getDest(), temp);
							boolean propResult = propagateChange(enc.getDest(), enc.getSource());
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
		//println ("[handleEdgeStartsWith] entered");
		//println ("[handleEdgeStartsWith] " + e.getSource().getName() + " and " + e.getDest().getName());
		boolean a1Changed, a2Changed;
		a1Changed = false; a2Changed = false;
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest()).concatenate(AutomatonExtra.makeAnyStringFixed());
		//println ("[handleEdgeStartsWith] a1 example: '" + a1.getShortestExample(true) + "'");
		//println ("[handleEdgeStartsWith] a2 example: '" + a2.getShortestExample(true) + "'");
		
		Automaton intersection = AutomatonExtra.intersection(a1, a2);
		if (intersection.isEmpty()) {
			elimanateCurrentLengths();
			//println ("[handleEdgeStartsWith] intersection empty");
			return false;
		}
		
		if (!a1.equals(intersection)) {a1Changed = true;}
		mapAutomaton.put(e.getSource(), intersection);
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
		
		Automaton temp = AutomatonExtra.startingSubstrings(intersection);
		Automaton intersection2 = AutomatonExtra.intersection(temp, a2);
		if (!a2.equals(intersection2)) {a2Changed = true;}
		mapAutomaton.put(e.getDest(), intersection2);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
		
		boolean result1, result2;
		result1 = true; result2 = true;
		if (a1Changed) {result1 = propagateChange(e.getSource(), e.getDest());}
		if (a2Changed) {result2 = propagateChange(e.getDest(), e.getSource());}
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
		//println ("[handleEdgeEndsWith] entered");
		boolean a1Changed, a2Changed;
		a1Changed = false; a2Changed = false;
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = AutomatonExtra.makeAnyStringFixed().concatenate(mapAutomaton.get(e.getDest()));
		Automaton intersection = AutomatonExtra.intersection(a1, a2);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeEndsWith] 1. intersection empty");
			elimanateCurrentLengths();
			return false;
		}
		
		if (!a1.equals(intersection)) {a1Changed = true;}
		mapAutomaton.put(e.getSource(), intersection);
		if (!e.getSource().isConstant()) e.getSource().setSolution(intersection.getShortestExample(true));
		
		
		Automaton temp = AutomatonExtra.endingSubstrings(intersection);
		Automaton intersection2 = AutomatonExtra.intersection(temp, a2);
		if (!a2.equals(intersection2)) {a2Changed = true;}
		mapAutomaton.put(e.getDest(), intersection2);
		if (!e.getDest().isConstant()) e.getDest().setSolution(intersection2.getShortestExample(true));
		
		boolean result1, result2;
		result1 = true; result2 = true;
		if (a1Changed) {result1 = propagateChange(e.getSource(), e.getDest());}
		if (a2Changed) {result2 = propagateChange(e.getDest(), e.getSource());}
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
			//println ("[handleEdgeCharAt] intersection empty, making index == -1 because the character could not be found anywhere");
			global_pc._addDet(Comparator.EQ, e.getIndex(), new IntegerConstant(-1));
			return false;
		}
		else {
			temp = AutomatonExtra.lengthAutomaton(e.getIndex().solutionInt());
			temp = temp.concatenate(Automaton.makeChar((char) e.getValue().solution()).concatenate(AutomatonExtra.makeAnyStringFixed()));
			intersection = AutomatonExtra.intersection(a1, temp);
			if (intersection.isEmpty()) {
				//println ("[handleEdgeCharAt] intersection empty, current index or value is not valid");
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
		if (!a1.equals(intersection)) a1Changed = true;
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
		if (!a2.equals(intersection)) a2Changed = true;
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
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
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
			return propResult;
		}
		//return true;
	}
	
	private static boolean handleEdgeIndexOf2 (EdgeIndexOf2 e) {
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
				//LinearOrIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				//loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.EQ, new IntegerConstant(-1)));
				global_pc._addDet (Comparator.EQ, e.getIndex(), -1);
				//global_pc._addDet(loic);
				return false;
			}
			temp = AutomatonExtra.lengthAutomaton(index);
			temp = temp.concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
			intersection = AutomatonExtra.intersection(a1, temp);
			//println ("[handleEdgeIndexOf] intersection example: " + intersection.getShortestExample(true));
			if (intersection.isEmpty()) {
				//println ("[handleEdgeIndexOf] 1. indexof could not be applyied at the current place");
				//LinearOrIntegerConstraints loic = elimanateCurrentLengthsConstraints();
				//loic.addToList(new LinearIntegerConstraint(e.getIndex(), Comparator.NE, new IntegerConstant(e.getIndex().solution())));
				global_pc._addDet(Comparator.NE, e.getIndex(), e.getIndex().solution());
				//global_pc._addDet(loic);
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
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(a2).concatenate(AutomatonExtra.makeAnyStringFixed());
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
			return propResult;
		}
		//return true;
	}
	
	private static boolean handleEdgeIndexOfChar (EdgeIndexOfChar e) {
		//println ("[handleEdgeIndexOf] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		//Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		String character = String.valueOf((char) e.getIndex().getExpression().solution());
		//First check if it is possible
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
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
			temp = temp.concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
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
				Automaton intersection2 = AutomatonExtra.intersection(Automaton.makeString(character), temp2);
				if (intersection2.isEmpty()) {
					//println ("[handleEdgeIndexOf] 2. indexof could not be applyied at the current place");
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
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
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
			return propResult;
		}
		//return true;
	}
	
	private static boolean handleEdgeIndexOfChar2 (EdgeIndexOfChar2 e) {
		//println ("[handleEdgeIndexOf] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		//Automaton a2 = mapAutomaton.get(e.getDest());
		int index = e.getIndex().solutionInt();
		String character = String.valueOf((char) e.getIndex().getExpression().solution());
		//First check if it is possible
		if (index > -1) {
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
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
			temp = temp.concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
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
				Automaton intersection2 = AutomatonExtra.intersection(Automaton.makeString(character), temp2);
				if (intersection2.isEmpty()) {
					//println ("[handleEdgeIndexOf] 2. indexof could not be applyied at the current place");
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
			Automaton temp = AutomatonExtra.makeAnyStringFixed().concatenate(Automaton.makeString(character)).concatenate(AutomatonExtra.makeAnyStringFixed());
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
			return propResult;
		}
		//return true;
	}

	
	private static boolean handleEdgeNotContains (EdgeNotContains e) {
		//println ("[handleEdgeNotContains] entered");
		//Should be done lazily
		
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
	
	private static boolean handleEdgeSubstring2Equal (EdgeSubstring2Equal e) {
		//println ("[handleEdgeSubstring2Equal] entered");
		Automaton a1 = mapAutomaton.get(e.getSource());
		Automaton a2 = mapAutomaton.get(e.getDest());
		
		Automaton temp = AutomatonExtra.substring(a1, e.getArgument1(), e.getArgument2());
		Automaton intersection = AutomatonExtra.intersection(temp, a2);
		if (intersection.isEmpty()) {
			//println ("[handleEdgeSubstring2Equal] intersection empty");
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
		temp2 = temp2.concatenate(intersection).concatenate(AutomatonExtra.makeAnyStringFixed());
		Automaton intersection2 = AutomatonExtra.intersection(a1, temp2);
		if (intersection2.isEmpty()) {
			//println ("[handleEdgeSubstring2Equal] intersection empty");
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
	
	private static boolean handleEdgeTrimEqual (EdgeTrimEqual e) {
		//println ("[handleEdgeTrimEqual] entered");
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
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		for (Vertex v: global_graph.getVertices()) {
			if (v.isConstant()) continue;
			loic.addToList(new LinearIntegerConstraint(v.getSymbolicLength(), Comparator.NE, new IntegerConstant(v.getLength())));
		}
		global_pc._addDet(loic);
	}
	
	private static LogicalORLinearIntegerConstraints elimanateCurrentLengthsConstraints() {
		LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
		for (Vertex v: global_graph.getVertices()) {
			if (v.isConstant()) continue;
			loic.addToList(new LinearIntegerConstraint(v.getSymbolicLength(), Comparator.NE, new IntegerConstant(v.getLength())));
		}
		return loic;
	}
	

}

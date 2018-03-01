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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import dk.brics.automaton.Automaton;
import dk.brics.automaton.State;
import dk.brics.automaton.StatePair;
import dk.brics.automaton.Transition;
import gov.nasa.jpf.util.LogManager;
import java.util.logging.Logger;

public class AutomatonExtra {
	
	//public static boolean logging = false;
  static Logger logger = LogManager.getLogger("stringsolver");
	
	/*
	 * Automaton.makeAnyString() produces a language that accepts words
	 * with ascii values of 0, 1 and other horrible characters.
	 * 
	 * This method produces a language with infinite set of 'normal' words included
	 */
	public static Automaton makeAnyStringFixed () {
		Automaton a = new Automaton();
		
		Transition t[] = new Transition[4];
		State acceptState = new State();
		acceptState.setAccept(true);
		t[0] = new Transition((char)32, (char)127, acceptState);
		State rejectState = new State ();
		rejectState.setAccept(false);
		t[1] = new Transition((char) 0, (char) 31, rejectState);
		t[2] = new Transition((char) 128, rejectState);
		t[3] = new Transition((char) 0, (char) 128, rejectState);
		
		acceptState.addTransition(t[0]);
		acceptState.addTransition(t[1]);
		acceptState.addTransition(t[2]);
		rejectState.addTransition(t[3]);
		
		a.setInitialState(acceptState);
		
		a.restoreInvariant();
		a.setDeterministic(true);
		
		return a;
	}
	
	/*
	 * Should be replaced with Automaton.repeat()
	 */
	public static Automaton star (Automaton a) {
		Automaton b = a.clone();
		b.determinize();
		
		State startState = b.getInitialState();
		Set<State> finalStates = b.getAcceptStates();
		startState.setAccept(true);
		Set<StatePair> epsilons = new HashSet<StatePair>();
		for (State s: finalStates) {
			epsilons.add(new StatePair(s, startState));
		}
		
		b.addEpsilons(epsilons);
		
		b.restoreInvariant();
		b.setDeterministic(false);
		return b;
	}
	
	public static List<State> statesReachable (Automaton a, int steps) {
		List<State> result = new ArrayList<State>();
		
		/* Assume determinzed */
		
		State startState = a.getInitialState();
		walkThrough (startState, 0, steps, result);
		
		return result;
	}
	
	private static void walkThrough (State current, int stepNumber, int maxSteps, List<State> result) {
		if (stepNumber > maxSteps) {
			return;
		}
		
		Integer distance = distanceFromStartState.get(current);
		if (distance == null) {
			distance = stepNumber;
			distanceFromStartState.put(current, distance);
		}
		
		if (stepNumber == maxSteps) {
			result.add(current);
		}
		
		Set<Transition> transitions = current.getTransitions();
		List<State> destinations = new ArrayList<State> ();
		for (Transition t: transitions) {
			State dest = t.getDest();
			if (!destinations.contains(dest)) {
				destinations.add(dest);
			}
		}
		
		for (State d: destinations) {
			walkThrough(d, stepNumber+1, maxSteps, result);
		}
		
	}
	private static Map<State, Integer> distanceFromStartState;
	public static Automaton substring (Automaton a, int start, int end) {
		if (start > end) {
			return null;
		}
		distanceFromStartState = new HashMap<State, Integer>();
		List<State> startStates = statesReachable(a, start);
		List<State> finalStates = statesReachable(a, end);
		/*List<State> startStates = new ArrayList<State>();
		for (Entry<State, Integer> e: distanceFromStartState.entrySet()) {
			int stateDistance = (int) e.getValue();
			if (stateDistance == start) {
				startStates.add(e.getKey());
			}
		}*/
		
		/* Create a copy of a without any transition from the finalstates to any further (not other) states*/
		Map<State, State> stateMap = new HashMap<State, State>();
		
		for (State s: a.getStates()) {
			State s1 = new State();
			s1.setAccept(s.isAccept());
			stateMap.put(s, s1);
		}
		
		Automaton b = new Automaton();
		for (State s: a.getStates()) {
			State newState = stateMap.get(s);
			for (Transition t: s.getTransitions()) {
				if (distanceFromStartState.get(t.getDest()) == null) {
					/* was not reachable within upper bound, so throw away*/
					continue;
				}
				State newDest = stateMap.get(t.getDest());
				newState.addTransition(new Transition(t.getMin(), t.getMax(), newDest));
			}
		}
		
		List<State> newStartStates = new ArrayList<State>(startStates.size());
		for (State s: startStates) {
			newStartStates.add(stateMap.get(s));
		}
		List<State> newFinalStates = new ArrayList<State>(finalStates.size());
		for (State s: finalStates) {
			newFinalStates.add(stateMap.get(s));
		}
		
		State newStartState = new State();
		State newFinalState = new State();
		newFinalState.setAccept(true);
		b.setInitialState(newStartState);
		Set<StatePair> epsilons = new HashSet<StatePair>();
		for (State s: newStartStates) {
			epsilons.add(new StatePair(newStartState, s));
		}
		for (State s: newFinalStates) {
			epsilons.add(new StatePair(s, newFinalState));
		}
		b.addEpsilons(epsilons);
		
		b.restoreInvariant();
		b.setDeterministic(false);
		
		b.determinize();
		
		/* Now I need to enforce that this new automata produces
		 * strings of only length end - start
		 */
		
		//b = b.minus(Automaton.makeEmptyString());
		Automaton exactLengthAutomata = Automaton.makeAnyChar();
		for (int i = 0; i < end - start - 1; i++) {
			exactLengthAutomata = exactLengthAutomata.concatenate(Automaton.makeAnyChar());
		}
		exactLengthAutomata = exactLengthAutomata.minus (Automaton.makeEmptyString());
		//System.out.println("Shotest example: '" + exactLengthAutomata.getShortestExample(true) + "'");
		b = b.intersection(exactLengthAutomata);
		
		return b;
	}
	
	public static Automaton startingSubstrings (Automaton a) {
		Automaton result = a.clone();
		result.setDeterministic(false);
		Map<State, State> stateMap = new HashMap<State, State>();
		for (State s1: a.getStates()) {
			State s2 = new State();
			s2.setAccept(s1.isAccept());
			stateMap.put(s1, s2);
		}
		State newFinalState = new State();
		newFinalState.setAccept(true);
		Set<StatePair> epsilons = new HashSet<StatePair>();
		for (State s: a.getStates()) {
			State newState = stateMap.get(s);
			epsilons.add(new StatePair(newState, newFinalState));
			for (Transition t: s.getTransitions()) {
				State newDest = stateMap.get(t.getDest());
				newState.addTransition(new Transition(t.getMin(), t.getMax(), newDest));
			}
		}
		result.setInitialState(stateMap.get(a.getInitialState()));
		result.addEpsilons(epsilons);
		
		result.restoreInvariant();
		result.setDeterministic(false);
		
		result.determinize();
		result.minimize();
		
		//result = result.union(Automaton.makeEmptyString());
		
		return result;
		
	}
	
	public static Automaton endingSubstrings (Automaton a) {
		Automaton result = a.clone();
		result.setDeterministic(false);
		Map<State, State> stateMap = new HashMap<State, State>();
		for (State s1: a.getStates()) {
			State s2 = new State();
			s2.setAccept(s1.isAccept());
			stateMap.put(s1, s2);
		}
		State newStartState = new State();
		newStartState.setAccept(true);
		Set<StatePair> epsilons = new HashSet<StatePair>();
		for (State s: a.getStates()) {
			State newState = stateMap.get(s);
			epsilons.add(new StatePair(newStartState, newState));
			for (Transition t: s.getTransitions()) {
				State newDest = stateMap.get(t.getDest());
				newState.addTransition(new Transition(t.getMin(), t.getMax(), newDest));
			}
		}
		result.setInitialState(newStartState);
		result.addEpsilons(epsilons);
		
		result.restoreInvariant();
		result.setDeterministic(false);
		
		result.determinize();
		result.minimize();
		
		//result = result.union(Automaton.makeEmptyString());
		
		return result;
		
	}
	
	public static Automaton substring (Automaton a, int start) {
		/* I don't think knowing the distances of states are important here */
		distanceFromStartState = new HashMap<State, Integer>();
		
		List<State> startStates = statesReachable(a, start);
		
		Map<State, State> stateMap = new HashMap<State, State>();
		
		for (State s: a.getStates()) {
			State s1 = new State();
			s1.setAccept(s.isAccept());
			stateMap.put(s, s1); /* s.clone? */
		}
		
		Automaton b = new Automaton();
		for (State s: a.getStates()) {
			State newState = stateMap.get(s);
			for (Transition t: s.getTransitions()) {
				State newDest = stateMap.get(t.getDest());
				newState.addTransition(new Transition(t.getMin(), t.getMax(), newDest));
			}
		}
		
		List<State> newStartStates = new ArrayList<State>(startStates.size());
		for (State s: startStates) {
			newStartStates.add(stateMap.get(s));
		}
		
		State newStartState = new State();
		b.setInitialState(newStartState);
		Set<StatePair> epsilons = new HashSet<StatePair>();
		for (State s: newStartStates) {
			epsilons.add(new StatePair(newStartState, s));
		}
		b.addEpsilons(epsilons);
		
		b.restoreInvariant();
		b.setDeterministic(false);
		
		b.determinize();
		
		return b;
	}
	
	/*
	 * It assumes that the automata is actually the concatenation of two
	 * automata's but they have been deliminated by the 'zero' (0) character
	 * before concatenation.
	 */
	public static Automaton[] splitByCharacter (char c, Automaton a) {
		Automaton[] result = new Automaton[2];
		Map<State, State> stateMapA1 = new HashMap<State, State>();
		Map<State, State> stateMapA2 = new HashMap<State, State>();
		
		a.determinize();
		a.minimize();
		
		result[0] = new Automaton();
		result[1] = new Automaton();
		stateMapA1 = new HashMap<State, State>();
		stateMapA2 = new HashMap<State, State>();
		
		/* Construct two new copies of a */
		for (State s: a.getStates()) {
			State s1 = new State();
			s1.setAccept(s.isAccept());
			stateMapA1.put(s, s1);
			State s2 = new State();
			s2.setAccept(s.isAccept());
			stateMapA2.put(s, s2);
		}
		
		State endStateOfA1 = new State();
		endStateOfA1.setAccept(true); /* Test this idea */
		State startStateOfA2 = new State();
		
		Set<StatePair> endA1EpsilonTransitions = new HashSet<StatePair>();
		Set<StatePair> startA2EpsilonTransitions = new HashSet<StatePair>();
		State stateWhereSplitOccurs = null;
		
		for (State s: a.getStates()) {
			for (Transition t: s.getSortedTransitions(false)) {
				if (t.getMin() == c) {
					/* Here is the split */
					State source = stateMapA1.get(s);
					endA1EpsilonTransitions.add(new StatePair(source, endStateOfA1));
					State dest = stateMapA2.get (t.getDest());
					startA2EpsilonTransitions.add (new StatePair(startStateOfA2, dest));
					stateWhereSplitOccurs = s;
				}
				//else if (t.getMin() < 128) {
				else {
					if (stateWhereSplitOccurs != null && stateWhereSplitOccurs == s) {
						/* Ignore the rest of this states transitions */
						logger.info("[splitByCharacter] Investigate");
						continue;
					}
					Transition t1 = new Transition(t.getMin(), t.getMax(), stateMapA1.get(t.getDest()));
					Transition t2 = new Transition(t.getMin(), t.getMax(), stateMapA2.get(t.getDest()));
					stateMapA1.get(s).addTransition(t1);
					stateMapA2.get(s).addTransition(t2);
				}
				 
			}
		}
		
		result[0].addEpsilons(endA1EpsilonTransitions);
		result[1].addEpsilons(startA2EpsilonTransitions);
		
		result[0].setInitialState(stateMapA1.get(a.getInitialState()));
		result[1].setInitialState(startStateOfA2);
		
		result[0].restoreInvariant();
		result[1].restoreInvariant();
		
		result[0].setDeterministic(false);
		result[1].setDeterministic(false);
		
		return result;
	}
	
	public static Automaton insertSingleChar (char c, Automaton a) {
		Automaton result = new Automaton();
		
		for (State s: a.getStates()) {
			for (Transition t: s.getTransitions()) {
				if (t.getMin() <= c && c <= t.getMax()) {
					//System.out.println("[Automatan Extra, insertSingleChar] character already inserted");
					logger.info ("[insertSingleChar] character already inserted");
					return a.clone();
				}
			}
		}
		
		Map<State, State> stateMap = new HashMap<State, State>();
		
		for (State s: a.getStates()) {
			State s1 = new State();
			s1.setAccept(s.isAccept());
			stateMap.put(s, s1);
		}
		
		List<Integer> specialCharsAlreadyInAutomata = new ArrayList<Integer>();
		
		for (State s: a.getStates()) {
			for (Transition t: s.getTransitions()) {
				Transition t1 = new Transition (t.getMin(), t.getMax(), stateMap.get(t.getDest()));
				stateMap.get(s).addTransition(t1);
				State s2 = new State();
				Transition t2 = new Transition(c, s2);
				stateMap.get(s).addTransition(t2);
				s2.addTransition(t1);
				
				if (t.getMax() > 127) {
					for (int i = 128; i <= t.getMax(); i++) {
						specialCharsAlreadyInAutomata.add(new Integer(i));
					}
				}
			}
			if (s.getTransitions().size() == 0) {
				State s2 = new State();
				s2.setAccept(true);
				Transition t2 = new Transition(c, s2);
				stateMap.get(s).addTransition(t2);
			}
		}
		
		result.setInitialState(stateMap.get (a.getInitialState()));
		
		Automaton b = Automaton.makeCharRange((char)32, (char)127);
		/* fix, to make it work with automata with more than one special char*/
		for (int i: specialCharsAlreadyInAutomata) {
			b = b.union(Automaton.makeChar((char) i));
		}
		b = b.minus (Automaton.makeChar(c));
		/* Hopefully forces only one of character c */
		Automaton filter = AutomatonExtra.star(b).concatenate(Automaton.makeChar(c).concatenate(AutomatonExtra.star(b.clone())));
		result = result.intersection(filter);
		
		result.restoreInvariant();
		result.setDeterministic(true);
		
		return result;
	}
	
	/*
	 * Does normal intersection, except adds all the characters > 128 that
	 * is needed.
	 */
	public static Automaton intersection (Automaton a, Automaton b) {
		List<Integer> specialCharsInA = new ArrayList<Integer>();
		List<Integer> specialCharsInB = new ArrayList<Integer>();
		List<Integer> missingCharsInA = new ArrayList<Integer>();
		List<Integer> missingCharsInB = new ArrayList<Integer>();
		
		for (State s: a.getStates()) {
			for (Transition t: s.getTransitions()) {
				for (int i = t.getMin(); i > 127 && i <= t.getMax(); i++) {
					if (!specialCharsInA.contains(new Integer(i)))
						specialCharsInA.add (new Integer (i));
				}
			}
		}
		
		if (specialCharsInA.size() > 100) {
			throw new RuntimeException("[AutomatanExtra, intersection] This was not considered");
		}
		
		//System.out.println("[AutomatanExtra, intersection] Specail chars in A: " + specialCharsInA);
		logger.info ("[intersection] Specail chars in A: " + specialCharsInA);
		
		
		for (State s: b.getStates()) {
			for (Transition t: s.getTransitions()) {
				for (int i = t.getMin(); i > 127 && i <= t.getMax(); i++) {
					if (!specialCharsInB.contains(new Integer(i)))
						specialCharsInB.add (new Integer (i));
				}
			}
		}

		if (specialCharsInB.size() > 100) {
			throw new RuntimeException("[AutomatanExtra, intersection] This was not considered");
		}
		//System.out.println("[AutomatanExtra, intersection] Specail chars in B: " + specialCharsInB);
		logger.info ("[intersection] Specail chars in B: " + specialCharsInB);
		
		for (Integer i: specialCharsInB) {
			if (!specialCharsInA.contains(i) && !missingCharsInA.contains(i)) {
				missingCharsInA.add(i);
			}
		}
		
		//System.out.println("[AutomatanExtra, intersection] Missing chars in A: " + missingCharsInA);
		logger.info("[intersection] Missing chars in A: " + missingCharsInA);

		
		for (Integer i: specialCharsInA) {
			if (!specialCharsInB.contains(i) && !missingCharsInB.contains(i)) {
				missingCharsInB.add(i);
			}
		}

		//System.out.println("[AutomatanExtra, intersection] Missing chars in B: " + missingCharsInB);
		logger.info ("[intersection] Missing chars in B: " + missingCharsInB);

		/* TODO: Improve performance */
		
		Automaton a_clone = a.clone();
		
		/*System.out.println(b);
		System.out.println("Finite: " + b.isFinite());*/
		
		Automaton b_clone = b.clone();
		
		for (int i: missingCharsInA) {
			a_clone = AutomatonExtra.insertSingleChar((char) i, a_clone);
		}
		

		
		for (int i: missingCharsInB) {
			b_clone = AutomatonExtra.insertSingleChar((char) i, b_clone);
		}
		
		//System.out.println(b_clone);
		
		return a_clone.intersection(b_clone);
	}
	
	public static Automaton getAutomatonAtPosition (Automaton a, int pos) {
		Automaton itter;
		if (pos == 0) {
			itter = a;
		}
		else {
			itter = Automaton.makeCharRange((char) 32, (char) 127);
			for (int i = 1; i < pos; i++) {
				itter = itter.concatenate(Automaton.makeCharRange((char) 32, (char) 127));
			}
		}
		itter = itter.concatenate(a).concatenate(AutomatonExtra.makeAnyStringFixed());
		return itter;
	}
	
	public static char getLowestCharacter (Automaton a) {
		char lowest = Character.MAX_VALUE;
		for (State s: a.getStates()) {
			for (Transition t: s.getTransitions()) {
				if (lowest > t.getMin()) {
					if (t.getMin() < 32) {
						lowest = 32;
					}
					else {
						lowest = t.getMin();
					}
				}
			}
		}
		return lowest;
	}
	
	public static char getHighestCharacter (Automaton a) {
		char highest = Character.MIN_VALUE;
		for (State s: a.getStates()) {
			for (Transition t: s.getTransitions()) {
				if (highest < t.getMax()) {
					if (t.getMax() > 127) {
						highest = 127;
					}
					else {
						highest = t.getMax();
					}
				}
			}
		}
		return highest;
	}
	
	public static List<Character> getExcludedCharacters (Automaton a, char low, char high) {
		List<Character> result = new ArrayList<Character>();
		boolean used[] = new boolean [high - low];
		for (State s: a.getStates()) {
			for (Transition t: s.getTransitions()) {
				for (int i = t.getMin(); i <= t.getMax(); i++) {
					used[i] = true;
				}
			}
		}
		/*only worry about characters between 32 and 127 (inclusive)*/
		for (int i = 32; i <= 127; i++) {
			if (used[i] == false) {
				result.add (new Character ((char)i));
			}
		}
		return result;
	}
	
	public static Automaton minus (Automaton a1, Automaton a2) {
		return AutomatonExtra.intersection(a1, a2.complement().intersection(AutomatonExtra.makeAnyStringFixed()));
	}
	
	public static Automaton lengthAutomaton (int length) {
		Automaton result = Automaton.makeEmptyString();
		for (int i = 0; i < length; i++) {
			result = result.concatenate(Automaton.makeCharRange((char) 32 , (char) 127));
		}
		return result;
	}
	
	public static Automaton reverseReplace (Automaton a, char c) {
		Automaton b = a.clone();
        for (State s : b.getStates()) {
            Set<Transition> transitions = s.getTransitions();
            for (Transition t : new ArrayList<Transition>(transitions)) {
                char min = t.getMin();
                char max = t.getMax();
                State dest = t.getDest();
                if (c < min || c > max) { // c is outside of reach
                    //transitions.remove(t);
                    transitions.add(new Transition(c, dest));
                    /*if (min < c) {
                        transitions.add(new Transition(min, (char) (c - 1), dest));
                    }
                    if (c < max) {
                        transitions.add(new Transition((char) (c + 1), max, dest));
                    }*/
                }
            }
        }
        b.setDeterministic(false);
        b.reduce();
        b.minimize();
        return b;
	}
}
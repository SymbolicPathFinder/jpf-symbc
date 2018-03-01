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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import aima.core.logic.propositional.parsing.ast.BinarySentence;
import aima.core.logic.propositional.parsing.ast.Sentence;
import aima.core.logic.propositional.parsing.ast.Symbol;
import aima.core.logic.propositional.parsing.ast.UnarySentence;

public class CNFExtra {
	public static List<List<Symbol>> remDup (List<List<Symbol>> input) {
		List<List<Symbol>> output = new ArrayList<List<Symbol>>();
		for (List<Symbol> c: input) {
			if (!output.contains(c)) {
				output.add(c);
			}
		}
		return output;
	}
	
	public static List<List<Symbol>> absorb (List<List<Symbol>> clauses) {
		List<List<Symbol>> clausesNotToInclude = new ArrayList<List<Symbol>>();

		for (int i = 0; i < clauses.size(); i++) {
			for (int j = i+1; j < clauses.size(); j++) {
				int result = contains(clauses.get(i), clauses.get(j));
				if (result != 0) {
					//System.out.println(clauses[i] + " contains " + clauses[j]);
					
					if (result == 1) {
						clausesNotToInclude.add(clauses.get(j));
					}
					else {
						clausesNotToInclude.add(clauses.get(i));
					}
				}
			}
		}
		
		List<List<Symbol>> result = new ArrayList<List<Symbol>>();
		for (List<Symbol> c: clauses) {
			//System.out.println(c);
			if (!clausesNotToInclude.contains(c)) {
				result.add(c);
			}
		}
		return result;
	}
	
	//Tells me which one is the smaller one
	private static int contains (List<Symbol> c1, List<Symbol> c2) {
		if (c1.size() == c2.size()) {
			return 0;
		}
		else if (c1.size() < c2.size()) {
			for (Symbol s1: c1) {
				if (!c2.contains(s1)) {
					return 0;
				}
			}
			return 1;
		}
		else {
			for (Symbol s1: c2) {
				if (!c1.contains(s1)) {
					return 0;
				}
			}
			return 2;
		}
	}
	
	public static Set<Sentence> extractClauses (Sentence s) {
		Set<Sentence> result = new HashSet<Sentence>();
		if (s instanceof Symbol) {
			result.add (s);
		}
		else if (s instanceof UnarySentence) {
			result.add(s);
		}
		else if (s instanceof BinarySentence) {
			BinarySentence bs = (BinarySentence) s;
			if (bs.getOperator().equals("OR")) {
				result.add(s);
			}
			else {
				result.addAll(extractClauses(bs.getFirst()));
				result.addAll(extractClauses(bs.getSecond()));
			}
		}
		return result;
	}
	
	public static List<List<Symbol>> idempotency (Set<Sentence> clauses) {
		//Assume s is CNF
		List<List<Symbol>> result = new ArrayList<List<Symbol>>();
		for (Sentence clause: clauses) {
			if (clause instanceof BinarySentence) {
				List<Symbol> symbols = extractSymbols (clause);
				List<Symbol> newClause = new ArrayList<Symbol>();
				//System.out.println("symbols: " + symbols);
				//Check for doubles
				for (Symbol s: symbols) {
					if (!newClause.contains(s)) {
						newClause.add(s);
					}
				}
				
				result.add(newClause);
			}
			else {
				List<Symbol> symbols = extractSymbols (clause);
				result.add (symbols);
			}
		}
		return result;
	}
	
	private static Sentence orClause  (List<Symbol> symbols) {
		if (symbols.size() == 1) {
			return symbols.get(0);
		}
		else { // size > 2
			BinarySentence result = new BinarySentence ("OR", symbols.get(0), symbols.get(1));
			for (int i = 2; i < symbols.size(); i++) {
				result = new BinarySentence ("OR", result, symbols.get(i));
			}
			return result;
		}
	}
	
	private static List<Symbol> extractSymbols (Sentence clause) {
		List<Symbol> result = new ArrayList<Symbol>();
		if (clause instanceof BinarySentence) {
			BinarySentence bs_clause = (BinarySentence) clause;
			if (bs_clause.getFirst() instanceof Symbol) {
				result.add ((Symbol)bs_clause.getFirst());
			}
			else if (bs_clause.getFirst() instanceof BinarySentence) {
				result.addAll (extractSymbols(bs_clause.getFirst()));
			}
			
			if (bs_clause.getSecond() instanceof Symbol) {
				result.add((Symbol) bs_clause.getSecond());
			}
			else if (bs_clause.getSecond() instanceof BinarySentence) {
				result.addAll (extractSymbols(bs_clause.getSecond()));
			}
		}
		else if (clause instanceof Symbol) {
			result.add((Symbol) clause);
		}
		return result;
	}
}

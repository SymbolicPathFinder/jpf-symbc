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

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.logging.Logger;

import cvc3.Expr;
import cvc3.FlagsMut;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;
import gov.nasa.jpf.symbc.string.graph.Edge;
import gov.nasa.jpf.symbc.string.graph.EdgeChar;
import gov.nasa.jpf.symbc.string.graph.EdgeCharAt;
import gov.nasa.jpf.symbc.string.graph.EdgeConcat;
import gov.nasa.jpf.symbc.string.graph.EdgeContains;
import gov.nasa.jpf.symbc.string.graph.EdgeEndsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeEqual;
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
import gov.nasa.jpf.symbc.string.graph.EdgeReplaceCharChar;
import gov.nasa.jpf.symbc.string.graph.EdgeStartsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeSubstring1Equal;
import gov.nasa.jpf.symbc.string.graph.EdgeSubstring2Equal;
import gov.nasa.jpf.symbc.string.graph.EdgeTrimEqual;
import gov.nasa.jpf.symbc.string.graph.StringGraph;
import gov.nasa.jpf.symbc.string.graph.Vertex;
import gov.nasa.jpf.util.LogManager;

public class TranslateToZ3 {
	static Logger logger = LogManager.getLogger("TranslateToZ3");

	protected static BVExpr expr;
	protected static FlagsMut flags = null;
	/* This number can be calculated beforehand */
	private static final int MAXVAR = 100000;
	/* Size of string */
	private static final int MAX_SIZE_OF_STRINGS = 100;

	private static Map<Vertex, BVExpr> map;
	private static int vectorOffset;

	private static int varIndex;

	// public static int totalTiming = 0;

	private static boolean printClauses = true;

	private static SymbolicConstraintsGeneral scg;

	private static PathCondition global_pc;

	private static Z3Interface z3Interface;

	private static final int MAX_ITERATIONS = 100; // number of symbolic string
													// expansions to try
	private static int remainingIterations = MAX_ITERATIONS; // quick fix to
																// prevent stack
																// overflows

	// most sign, first letter
	public static boolean isSat(StringGraph g, PathCondition pc) {
		remainingIterations--;
		if (remainingIterations < 0) {
			remainingIterations = MAX_ITERATIONS;
			// println("no more iterations remains");
			return false;
		}

		// System.out.println("#STRING-Z3 solving new graph:" + g);
		/* check if there was a timeout */
		SymbolicStringConstraintsGeneral.checkTimeOut();
		// println ("[isSat] graph after preprocessing: " + g.toDot());
		global_pc = pc;
		if (scg == null)
			scg = new SymbolicConstraintsGeneral();
		expr = null;
		// println ("[isSat] Bitvector: PC passed on: " + pc.header);
		map = new HashMap<Vertex, BVExpr>();

		if (z3Interface == null) {
			try {
				z3Interface = new Z3Interface();
			} catch (Exception e) {
				throw new RuntimeException("Could not load up z3\nMake sure the Z3 binary is in lib directory");
			}
		}

		// println ("[isSat] Walking through the edges");
		for (Edge e : g.getEdges()) {
			if (e instanceof EdgeStartsWith) {
				handleEdgeStartsWith((EdgeStartsWith) e);
			} else if (e instanceof EdgeNotStartsWith) {
				handleEdgeNotStartsWith((EdgeNotStartsWith) e);
			} else if (e instanceof EdgeEqual) {
				handleEdgeEqual((EdgeEqual) e);
			} else if (e instanceof EdgeNotEqual) {
				handleEdgeNotEqual((EdgeNotEqual) e);
			} else if (e instanceof EdgeTrimEqual) {
				handleEdgeTrim((EdgeTrimEqual) e);
			} else if (e instanceof EdgeCharAt) {
				handleEdgeCharAt((EdgeCharAt) e);
			} else if (e instanceof EdgeNotCharAt) {
				handleEdgeNotCharAt((EdgeNotCharAt) e);
			} else if (e instanceof EdgeConcat) {
				handleEdgeConcat((EdgeConcat) e);
			} else if (e instanceof EdgeContains) {
				handleEdgeContains((EdgeContains) e);
			} else if (e instanceof EdgeEndsWith) {
				handleEdgeEndsWith((EdgeEndsWith) e);
			} else if (e instanceof EdgeIndexOf) {
				handleEdgeIndexOf((EdgeIndexOf) e);
			} else if (e instanceof EdgeIndexOfChar) {
				handleEdgeIndexOfChar((EdgeIndexOfChar) e);
			} else if (e instanceof EdgeLastIndexOfChar) {
				handleEdgeLastIndexOfChar((EdgeLastIndexOfChar) e);
			} else if (e instanceof EdgeLastIndexOfChar2) {
				handleEdgeLastIndexOfChar2((EdgeLastIndexOfChar2) e);
			} else if (e instanceof EdgeIndexOf2) {
				// println ("[isSat] EdgeIndexOf2");
				handleEdgeIndexOf2((EdgeIndexOf2) e);
			} else if (e instanceof EdgeIndexOfChar2) {
				// println ("[isSat] EdgeIndexOfChar2");
				handleEdgeIndexOfChar2((EdgeIndexOfChar2) e);
			} else if (e instanceof EdgeNotContains) {
				handleEdgeNotContains((EdgeNotContains) e);
			} else if (e instanceof EdgeNotEndsWith) {
				handleEdgeNotEndsWith((EdgeNotEndsWith) e);
			} else if (e instanceof EdgeSubstring1Equal) {
				handleEdgeSubstring1Equal((EdgeSubstring1Equal) e);
			} else if (e instanceof EdgeSubstring2Equal) {
				handleEdgeSubstring2Equal((EdgeSubstring2Equal) e);
			} else if (e instanceof EdgeReplaceCharChar) {
				handleEdgeReplaceCharChar((EdgeReplaceCharChar) e);
			} else {
				throw new RuntimeException("Edge not supported: " + e.getClass().toString());
			}
			if (expr != null) {
				// println ("[isSat] expr: " + expr.toString());
			}
		}
		// println ("[isSat] Done walking through the edges");
		/* TODO: Remove */
		if (expr == null)
			return true;
		// println(expr.toString());
		// vc.loadFile(fileName);
		// vc.push();
		// long timing = System.currentTimeMillis();

		// return true;
		// SatResult result = vc.checkUnsat(expr);
		try {
			// println ("[isSat] Starting up Z3...");
			z3Interface = new Z3Interface();
			// println ("[isSat] started, sending message...");
			z3Interface.sendMessage(getSMTLibMsg());
			// println ("[isSat] Done");
		} catch (IOException ex) {
			throw new RuntimeException("Could not send z3 message: " + ex.getMessage());
		}
		// System.out.println("Solution: " + z3Interface.getAns());
		// totalTiming += System.currentTimeMillis() - timing;
		if (z3Interface.sat == false) {
			// println ("[isSat] Current solutions is unsat, extending lengts");
			LogicalORLinearIntegerConstraints loic = new LogicalORLinearIntegerConstraints();
			for (Vertex v : g.getVertices()) {
				if (!v.getName().startsWith("CHAR"))
					loic.addToList(new LinearIntegerConstraint(v.getSymbolicLength(), Comparator.NE,
							new IntegerConstant(v.getSymbolicLength().solution())));
			}
			for (Edge e : g.getEdges()) {
				if (e instanceof EdgeChar) {
					EdgeChar eca = (EdgeChar) e;
					loic.addToList(new LinearIntegerConstraint(eca.getIndex(), Comparator.NE,
							new IntegerConstant(eca.getIndex().solution())));
					loic.addToList(new LinearIntegerConstraint(eca.getValue(), Comparator.NE,
							new IntegerConstant(eca.getValue().solution())));
				} else if (e instanceof EdgeIndexOf) {
					EdgeIndexOf eio = (EdgeIndexOf) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE,
							new IntegerConstant(eio.getIndex().solution())));
				} else if (e instanceof EdgeIndexOfChar) {
					EdgeIndexOfChar eio = (EdgeIndexOfChar) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE,
							new IntegerConstant(eio.getIndex().solution())));
					IntegerExpression charSought = eio.getIndex().getExpression();
					loic.addToList(new LinearIntegerConstraint(charSought, Comparator.NE,
							new IntegerConstant(charSought.solution())));
				} else if (e instanceof EdgeLastIndexOfChar) {
					EdgeLastIndexOfChar eio = (EdgeLastIndexOfChar) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE,
							new IntegerConstant(eio.getIndex().solution())));
				} else if (e instanceof EdgeLastIndexOfChar2) {
					EdgeLastIndexOfChar2 eio = (EdgeLastIndexOfChar2) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE,
							new IntegerConstant(eio.getIndex().solution())));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinDist(), Comparator.NE,
							new IntegerConstant(eio.getIndex().getMinDist().solution())));
				} else if (e instanceof EdgeIndexOf2) {
					EdgeIndexOf2 eio = (EdgeIndexOf2) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE,
							new IntegerConstant(eio.getIndex().solution())));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinIndex(), Comparator.NE,
							new IntegerConstant(eio.getIndex().getMinIndex().solution())));
				} else if (e instanceof EdgeIndexOfChar2) {
					EdgeIndexOfChar2 eio = (EdgeIndexOfChar2) e;
					loic.addToList(new LinearIntegerConstraint(eio.getIndex(), Comparator.NE,
							new IntegerConstant(eio.getIndex().solution())));
					loic.addToList(new LinearIntegerConstraint(eio.getIndex().getMinDist(), Comparator.NE,
							new IntegerConstant(eio.getIndex().getMinDist().solution())));
				} else if (e instanceof EdgeSubstring1Equal) {
					EdgeSubstring1Equal es1e = (EdgeSubstring1Equal) e;
					if (es1e.getArgument1Symbolic() != null) {
						loic.addToList(new LinearIntegerConstraint(es1e.getArgument1Symbolic(), Comparator.NE,
								new IntegerConstant(es1e.getArgument1Symbolic().solution())));
					}
				} else if (e instanceof EdgeSubstring2Equal) {
					EdgeSubstring2Equal es2e = (EdgeSubstring2Equal) e;
					if (es2e.getSymbolicArgument1() != null) {
						loic.addToList(new LinearIntegerConstraint(es2e.getSymbolicArgument1(), Comparator.NE,
								new IntegerConstant(es2e.getSymbolicArgument1().solution())));
					}
					if (es2e.getSymbolicArgument2() != null) {
						loic.addToList(new LinearIntegerConstraint(es2e.getSymbolicArgument2(), Comparator.NE,
								new IntegerConstant(es2e.getSymbolicArgument2().solution())));
					}
				}
			}
			// println ("[isSat] loic: " + loic);
			pc._addDet(loic);
			// println ("[isSat] firing up integer constraint solver");
			if (scg.isSatisfiable(pc)) {
				// println ("[isSat] integer constriant solver found it to be
				// sat, solving...");
				scg.solve(pc);
				pc.flagSolved = true;
				// println ("[isSat] solved PC: " + pc.header);

				return isSat(g, pc); // TODO: Prevent infinite looping
			} else {
				// println ("[isSat] With the added constraint, could not be
				// solved");

				return false;
			}
		} else if (z3Interface.sat) {
			Map<String, String> ans = z3Interface.getAns();
			// println(model.toString());

			for (Entry<String, String> entry : ans.entrySet()) {
				int reverseMapKey = Integer.parseInt(entry.getKey().substring(3));
				String vertexName = BVVar.reverseMap.get(reverseMapKey);
				String rawData = entry.getValue();
				rawData = fromRawData(rawData);
				//// println (vertexName + " = " + rawData);
				Vertex v = g.findVertex(vertexName);
				if (!v.isConstant()) {
					v.setSolution(rawData);
				}
			}
			// System.out.//println("Satisfiable (Invalid)\n");
			return true;
		} else {
			return false;
		}

		// return true;
	}

	private static String fromRawData(String data) {
		StringBuilder result = new StringBuilder();
		StringBuilder word = new StringBuilder();
		int count = 0;
		// Skip "0bin"
		for (int i = 0; i < data.length(); i++) {
			if (count == 8) {
				result.append((char) Integer.parseInt(word.toString(), 2));
				word = new StringBuilder();
				count = 0;
			}
			word.append(data.charAt(i));
			count++;
		}
		result.append((char) Integer.parseInt(word.toString(), 2));
		return result.toString();
	}

	private static BVExpr startsWith(Edge e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			// println ("startsWith Branch 1");
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());

			BVExpr temp = new BVExtract(source, e.getSource().getLength() * 8 - 1,
					(e.getSource().getLength() - e.getDest().getLength() + 1) * 8 - 8);
			return (new BVEq(temp, dest));

		} else if (!e.getSource().isConstant()) {
			// println ("startsWith Branch 2 " + e);
			BVExpr source = getBVExpr(e.getSource());
			String constant = e.getDest().getSolution();
			// println ("[startsWith] constant: " + constant);
			BVExpr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				BVExpr temp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
						(e.getSource().getLength() - i) * 8 - 8);
				char character = constant.charAt(i);
				if (lit == null) {
					lit = new BVEq(temp, new BVConst(character));
				} else {
					lit = new BVAnd(lit, new BVEq(temp, new BVConst(character)));
				}
			}
			// println ("[startsWith] returning: " + lit);
			return (lit);
		} else if (!e.getDest().isConstant()) {
			// println ("startsWith Branch 3 " + e);
			BVExpr dest = getBVExpr(e.getDest());
			String constant = e.getSource().getSolution();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
						(e.getDest().getLength() - i) * 8 - 8);
				char character = constant.charAt(i);
				lit = and(lit, new BVEq(temp, new BVConst(character)));
			}
			/*
			 * for (int j = 0; j < constant.length(); j++) { BVExpr lit = null;
			 * for (int i = 0; i <= j; i++) { BVExpr temp = new BVExtract(dest,
			 * (e.getSource().getLength() - i) * 8 - 1,
			 * (e.getSource().getLength() - i) * 8 - 8); char character =
			 * constant.charAt(i); if (lit == null) { lit = new BVEq (temp, new
			 * BVConst(character)); } else { lit = new BVAnd (lit, new BVEq
			 * (temp, new BVConst(character))); } } if (listOfLit == null) {
			 * listOfLit = lit; } else { listOfLit = new BVOr (listOfLit, lit);
			 * } }
			 */
			return (lit);
		} else {
			String sourceConstant = e.getSource().getSolution();
			String destConstant = e.getDest().getSolution();
			// println ("[startsWith] sourceConstant: " + sourceConstant);
			// println ("[startsWith] destConstant: " + destConstant);

			if (sourceConstant.startsWith(destConstant)) {
				return new BVTrue();
			} else {
				return new BVFalse();
			}
		}
		// println ("[startsWith] returning null: " + e.toString());
		// return null;
	}

	private static void handleEdgeStartsWith(EdgeStartsWith e) {
		post(startsWith(e));
	}

	private static void handleEdgeNotStartsWith(EdgeNotStartsWith e) {
		if (e.getSource().getLength() < e.getDest().getLength())
			return;
		post(new BVNot(startsWith(e)));
	}

	private static void handleEdgeReplaceCharChar(EdgeReplaceCharChar e) {
		BVExpr source = getBVExpr(e.getSource());
		BVExpr dest = getBVExpr(e.getDest());

		BVExpr setOflit = null;
		BVExpr lit;
		// println ("[handleEdgeReplaceCharChar] e.getSource().getLength(): " +
		// e.getSource().getLength());
		// if s[i] == toReplace then d[i] == replacedChar otherwise s[i] == d[i]
		for (int i = 1; i <= e.getSource().getLength(); i++) {
			BVExpr extSrc = new BVExtract(source, i * 8 - 1, i * 8 - 8);
			BVExpr extDst = new BVExtract(dest, i * 8 - 1, i * 8 - 8);
			lit = new BVITE(new BVEq(extSrc, new BVConst(e.getC1())), new BVEq(extDst, new BVConst(e.getC2())),
					new BVEq(extSrc, extDst));
			setOflit = and(setOflit, lit);
		}
		// println ("[handleEdgeReplaceCharChar] setOflit: " + setOflit);
		post(setOflit);

		setOflit = null;
		for (int i = 1; i <= e.getSource().getLength(); i++) {
			lit = new BVNot(new BVEq(new BVExtract(dest, i * 8 - 1, i * 8 - 8), new BVConst(e.getC1())));
			setOflit = and(setOflit, lit);
		}
		post(setOflit);
	}

	private static BVExpr endsWith(Edge e) {
		// println ("endsWith entered");
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			// println ("endsWith branch 1");
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());

			BVExpr temp = new BVExtract(source, e.getDest().getLength() * 8 - 1, 0);
			return (new BVEq(temp, dest));

		} else if (!e.getSource().isConstant()) {
			// println ("endsWith branch 2");
			BVExpr source = getBVExpr(e.getSource());
			String constant = e.getDest().getSolution();
			BVExpr lit = null;
			for (int i = constant.length() - 1; i >= 0; i--) {
				BVExpr temp = new BVExtract(source, (constant.length() - i) * 8 - 1, (constant.length() - i) * 8 - 8);
				char character = constant.charAt(i);
				if (lit == null) {
					lit = new BVEq(temp, new BVConst(character));
				} else {
					lit = new BVAnd(lit, new BVEq(temp, new BVConst(character)));
				}

			}
			return (lit);
		} else if (!e.getDest().isConstant()) {
			// println ("endsWith branch 3");
			BVExpr dest = getBVExpr(e.getDest());
			String constant = e.getSource().getSolution();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
						(e.getDest().getLength() - i) * 8 - 8);
				char character = constant.charAt(i + (constant.length() - e.getDest().getLength()));
				lit = and(lit, new BVEq(temp, new BVConst(character)));
			}
			/*
			 * for (int j = 0; j < constant.length(); j++) { BVExpr lit = null;
			 * for (int i = constant.length() - 1; i >= constant.length() - j -
			 * 1; i--) { BVExpr temp = new BVExtract(dest, (constant.length() -
			 * i) * 8 - 1, (constant.length() - i) * 8 - 8); char character =
			 * constant.charAt(i); if (lit == null) { lit = new BVEq(temp, new
			 * BVConst(character)); } else { lit = new BVAnd(lit, new BVEq(temp,
			 * new BVConst(character))); }
			 * 
			 * } if (listOfLit == null) { listOfLit = lit; } else { listOfLit =
			 * new BVOr(listOfLit, lit); } }
			 */
			return (lit);
		} else {
			String constant1 = e.getSource().getSolution();
			String constant2 = e.getDest().getSolution();
			if (constant1.endsWith(constant2)) {
				return new BVTrue();
			} else {
				return new BVFalse();
			}
		}
		// println ("endsWith no branch");
		// return null;
	}

	private static void handleEdgeEndsWith(EdgeEndsWith e) {
		// println ("handleEdgeEndsWith " + e);
		post(endsWith(e));
	}

	private static void handleEdgeNotEndsWith(EdgeNotEndsWith e) {
		// println ("handleEdgeNotEndsWith");
		if (e.getDest().getLength() > e.getSource().getLength()) {
			return;
		}
		post(new BVNot(endsWith(e)));
	}

	private static BVExpr equal(Edge e) {
		// println ("[equal] e: " + e.toString());
		if (e.getSource().getLength() != e.getDest().getLength()) {
			return new BVFalse();
		}
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());
			return new BVEq(source, dest);
		} else if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			String constant = e.getDest().getSolution();
			BVExpr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				char c = constant.charAt(i);
				BVExpr temp = new BVExtract(source, (constant.length() - i) * 8 - 1, (constant.length() - i) * 8 - 8);
				BVExpr cons = new BVConst(c);
				lit = and(lit, new BVEq(temp, cons));
			}
			return lit;
		} else if (!e.getDest().isConstant()) {
			BVExpr dest = getBVExpr(e.getDest());
			String constant = e.getSource().getSolution();
			BVExpr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				char c = constant.charAt(i);
				BVExpr temp = new BVExtract(dest, (constant.length() - i) * 8 - 1, (constant.length() - i) * 8 - 8);
				BVExpr cons = new BVConst(c);
				lit = and(lit, new BVEq(temp, cons));
			}
			return lit;

		} else {
			String constant1 = e.getSource().getSolution();
			String constant2 = e.getDest().getSolution();
			if (constant1.equals(constant2)) {
				return new BVTrue();
			} else {
				return new BVFalse();
			}
		}
		// return null;
	}

	private static void handleEdgeNotEqual(EdgeNotEqual e) {
		if (e.getSource().getLength() != e.getDest().getLength()) {
			return;
		}
		post(new BVNot(equal(e)));
	}

	private static void handleEdgeEqual(EdgeEqual e) {
		// println ("[handleEdgeEqual] entered: " + e.toString());
		post(equal(e));
	}

	private static void handleEdgeTrim(EdgeTrimEqual e) {
		logger.info("[handleEdgeTrim] entered handleEdgeTrim " + e);
		if (e.getSource().getLength() == e.getDest().getLength()) {
			logger.info("[handleEdgeTrim] 1. posting: " + equal(e));
			post(equal(e));
			return;
		}

		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			// println ("[handleEdgeTrim] branch 1");
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());

			int diff = e.getSource().getLength() - e.getDest().getLength() + 1;

			BVExpr listOflit = null;
			for (int i = 0; i < diff; i++) {
				BVExpr lit = null;
				BVExpr sourceTemp, destTemp;
				for (int j = 0; j < i; j++) {
					sourceTemp = new BVExtract(source, (e.getSource().getLength() - j) * 8 - 1,
							(e.getSource().getLength() - j) * 8 - 8);
					lit = and(lit, new BVEq(sourceTemp, new BVConst(' ')));
				}
				sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
						(e.getSource().getLength() - i - e.getDest().getLength()) * 8 - 1 + 1);
				// destTemp = new BVExtract(dest, (e.getDest().getLength() - (j
				// - i)) * 8 - 1, (e.getDest().getLength() - (j - i)) * 8 - 8);
				// println ("[handleEdgeTrim] 2. lit before: " + lit);
				lit = and(lit, new BVEq(sourceTemp, dest));
				// println ("[handleEdgeTrim] 2. lit so far: " + lit);
				for (int j = i + e.getDest().getLength(); j < e.getSource().getLength(); j++) {
					sourceTemp = new BVExtract(source, (e.getSource().getLength() - j) * 8 - 1,
							(e.getSource().getLength() - j) * 8 - 8);
					lit = and(lit, new BVEq(sourceTemp, new BVConst(' ')));
				}
				listOflit = or(listOflit, lit);
			}
			// println ("[handleEdgeTrim] 2. posting: " + listOflit);
			post(listOflit);

		} else if (!e.getSource().isConstant()) {
			// println ("[handleEdgeTrim] branch 2");
			BVExpr source = getBVExpr(e.getSource());
			String constant = e.getDest().getSolution();
			int diff = e.getSource().getLength() - e.getDest().getLength() + 1;
			String allPossiblAnswers[] = new String[diff];
			for (int i = 0; i < diff; i++) {
				StringBuilder sb = new StringBuilder();
				for (int j = 0; j < i; j++) {
					sb.append(" ");
				}
				sb.append(constant);
				for (int j = i + constant.length(); j < e.getSource().getLength(); j++) {
					sb.append(" ");
				}
				allPossiblAnswers[i] = sb.toString();
			}
			BVExpr listOfLit = null;
			for (String s : allPossiblAnswers) {
				// println ("[handleEdgeTrim] possible answer: '" + s + "'");
				BVExpr lit = null;
				for (int i = 0; i < s.length(); i++) {
					BVExpr temp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr bvconst = new BVConst(s.charAt(i));
					BVExpr toplace = new BVEq(temp, bvconst);
					if (lit == null) {
						lit = toplace;
					} else {
						lit = new BVAnd(lit, toplace);
					}
				}
				if (listOfLit == null) {
					listOfLit = lit;
				} else {
					listOfLit = new BVOr(listOfLit, lit);
				}
			}
			// println ("[handleEdgeTrim] 3. posting: " + listOfLit);
			post(listOfLit);
		} else if (!e.getDest().isConstant()) {
			// println ("[handleEdgeTrim] branch 3");
			BVExpr dest = getBVExpr(e.getDest());
			String constant = e.getSource().getSolution().trim();
			if (e.getDest().getLength() != constant.length()) {
				throw new RuntimeException("Preprocessor fudged up");
			}
			BVExpr lit = null;
			for (int i = 0; i < constant.length(); i++) {
				BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
						(e.getDest().getLength() - i) * 8 - 8);
				lit = and(lit, new BVEq(temp, new BVConst(constant.charAt(i))));
			}
			// println ("[handleEdgeTrim] 4. posting: " + lit);
			post(lit);
		}
	}

	public static void handleEdgeCharAt(EdgeCharAt e) {
		if (!e.getSource().isConstant()) {
			BVExpr eqExpr = prepareEqSymbolicSrc(e);
			post(eqExpr);
		} else {
			List<BVExpr> exps = prepareEqConstantSrc(e);
			for (BVExpr exp : exps) {
				post(exp);
			}
		}
	}

	private static void handleEdgeNotCharAt(EdgeNotCharAt e) {
		if (!e.getSource().isConstant()) {
			BVExpr eqExpr = prepareEqSymbolicSrc(e);
			post(new BVNot(eqExpr));

		} else {
			List<BVExpr> exps = prepareEqConstantSrc(e);

			if (exps.size() == 1) {
				BVExpr exp = exps.get(0);
				post(new BVNot(exp));

			} else { // apply De Morgan' law
				BVExpr first = ((BVNot) exps.get(0)).expr;
				BVExpr second = ((BVNot) exps.get(1)).expr;

				BVOr orExpr = new BVOr(first, second);
				for (int i = 2; i < exps.size(); i++) {
					BVExpr exp = ((BVNot) exps.get(i)).expr;
					orExpr = new BVOr(exp, orExpr);
				}
				post(new BVNot(orExpr));
			}
		}
	}

	private static List<BVExpr> prepareEqConstantSrc(EdgeChar e) {
		List<BVExpr> exprs = new ArrayList<BVExpr>();

		String constant = e.getSource().getSolution();
		char c = e.getValue().solutionChar();
		int index = e.getIndex().solutionInt();
		if (index > -1) { // char c is present at the string
			BVExpr temp1 = new BVConst(constant.charAt(index));
			BVExpr temp2 = new BVConst(c);
			exprs.add(new BVEq(temp1, temp2));
		} else { // char c is not present at the string
			for (int i = 0; i < constant.length(); i++) {
				BVExpr temp1 = new BVConst(constant.charAt(i));
				BVExpr temp2 = new BVConst(c);
				exprs.add((new BVNot(new BVEq(temp1, temp2))));
			}
		}

		return exprs;
	}

	private static BVExpr prepareEqSymbolicSrc(EdgeChar e) {
		BVExpr source = getBVExpr(e.getSource());
		char c = (char) e.getValue().solution();
		int index = e.getIndex().solutionInt();
		BVExpr temp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1,
				(e.getSource().getLength() - index) * 8 - 8);
		BVExpr cons = new BVConst(c);
		BVExpr eqExpr = new BVEq(temp, cons);
		return eqExpr;
	}

	private static void handleEdgeConcat(EdgeConcat e) {
		if (e.getDest().isConstant()) {
			// println ("[handleEdgeConcat] dest is constant");
			if (!e.getSources().get(0).isConstant() && !e.getSources().get(1).isConstant()) {

				String constant = e.getDest().getSolution();
				BVExpr source1 = getBVExpr(e.getSources().get(0));
				BVExpr source2 = getBVExpr(e.getSources().get(1));
				BVExpr lit = null;
				for (int i = 0; i < e.getSources().get(0).getLength(); i++) {
					BVExpr temp = new BVExtract(source1, (e.getSources().get(0).getLength() - i) * 8 - 1,
							(e.getSources().get(0).getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(constant.charAt(i));
					lit = and(lit, new BVEq(temp, cons));
				}
				for (int i = 0; i < e.getSources().get(1).getLength(); i++) {
					BVExpr temp = new BVExtract(source2, (e.getSources().get(1).getLength() - i) * 8 - 1,
							(e.getSources().get(1).getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(constant.charAt(i + e.getSources().get(0).getLength()));
					lit = and(lit, new BVEq(temp, cons));
				}
				post(lit);
			} else if (!e.getSources().get(0).isConstant()) {
				String destConstant = e.getDest().getSolution();
				String source2Constant = e.getSources().get(1).getSolution();
				BVExpr source1 = getBVExpr(e.getSources().get(0));
				if (!destConstant.endsWith(source2Constant))
					throw new RuntimeException("This should not happen");
				BVExpr lit = null;
				for (int i = 0; i < e.getSources().get(0).getLength(); i++) {
					BVExpr temp = new BVExtract(source1, (e.getSources().get(0).getLength() - i) * 8 - 1,
							(e.getSources().get(0).getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(destConstant.charAt(i));
					lit = and(lit, new BVEq(temp, cons));
				}
				post(lit);
			} else if (!e.getSources().get(1).isConstant()) {
				String destConstant = e.getDest().getSolution();
				String source1Constant = e.getSources().get(0).getSolution();
				BVExpr source2 = getBVExpr(e.getSources().get(1));
				if (!destConstant.startsWith(source1Constant))
					throw new RuntimeException("This should not happen");
				BVExpr lit = null;
				for (int i = e.getSources().get(0).getLength(); i < e.getDest().getLength(); i++) {
					BVExpr temp = new BVExtract(source2, (e.getDest().getLength() - i) * 8 - 1,
							(e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(destConstant.charAt(i));
					lit = and(lit, new BVEq(temp, cons));
				}
				post(lit);
			}

		} else {
			// println ("[handleEdgeConcat] dest is NOT constant");
			// e.getDest().isConstant() == false
			if (!e.getSources().get(0).isConstant() && !e.getSources().get(1).isConstant()) {
				// println ("[handleEdgeConcat] both sources is NOT constant");
				BVExpr source1 = getBVExpr(e.getSources().get(0));
				BVExpr source2 = getBVExpr(e.getSources().get(1));
				BVExpr dest = getBVExpr(e.getDest());
				BVExpr lit = null;
				BVExpr temp = new BVExtract(dest, (e.getDest().getLength()) * 8 - 1,
						(e.getDest().getLength() - e.getSources().get(0).getLength() + 1) * 8 - 8);
				lit = and(lit, new BVEq(temp, source1));
				// println ("[handleEdgeConcat] " + e.getDest().getLength() + "
				// - " + e.getSources().get(0).getLength());
				temp = new BVExtract(dest, (e.getDest().getLength() - e.getSources().get(0).getLength()) * 8 - 1, 0);
				lit = and(lit, new BVEq(temp, source2));
				post(lit);
			} else if (!e.getSources().get(0).isConstant()) {
				BVExpr source1 = getBVExpr(e.getSources().get(0));
				String source2Cons = e.getSources().get(1).getSolution();
				BVExpr dest = getBVExpr(e.getDest());
				BVExpr lit = null;
				for (int i = 0; i < e.getSources().get(0).getLength(); i++) {
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
							(e.getDest().getLength() - i) * 8 - 8);
					BVExpr sourceTemp = new BVExtract(source1, (e.getSources().get(0).getLength() - i) * 8 - 1,
							(e.getSources().get(0).getLength() - i) * 8 - 8);
					lit = and(lit, new BVEq(destTemp, sourceTemp));
				}
				for (int i = 0; i < source2Cons.length(); i++) {
					char character = source2Cons.charAt(i);
					BVExpr temp = new BVExtract(dest,
							(e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 1,
							(e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(character);
					lit = and(lit, new BVEq(temp, cons));
				}
				post(lit);
			} else if (!e.getSources().get(1).isConstant()) {
				String source1Cons = e.getSources().get(0).getSolution();
				BVExpr source2 = getBVExpr(e.getSources().get(1));
				BVExpr dest = getBVExpr(e.getDest());
				BVExpr lit = null;
				for (int i = 0; i < source1Cons.length(); i++) {
					char character = source1Cons.charAt(i);
					BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
							(e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(character);
					lit = and(lit, new BVEq(temp, cons));
				}
				for (int i = 0; i < e.getSources().get(1).getLength(); i++) {
					BVExpr destTemp = new BVExtract(dest,
							(e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 1,
							(e.getDest().getLength() - e.getSources().get(0).getLength() - i) * 8 - 8);
					BVExpr source2Temp = new BVExtract(source2, (e.getSources().get(1).getLength() - i) * 8 - 1,
							(e.getSources().get(1).getLength() - i) * 8 - 8);
					lit = and(lit, new BVEq(destTemp, source2Temp));
				}
				post(lit);
			}
		}
	}

	private static BVExpr contains(Edge e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			// println ("contains branch 1");
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());
			int diff = e.getSource().getLength() - e.getDest().getLength();
			BVExpr listOfLit = null;
			for (int i = 0; i <= diff; i++) {
				BVExpr lit = null;
				for (int j = i; j < i + e.getDest().getLength(); j++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - j) * 8 - 1,
							(e.getSource().getLength() - j) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - (j - i)) * 8 - 1,
							(e.getDest().getLength() - (j - i)) * 8 - 8);
					lit = and(lit, new BVEq(sourceTemp, destTemp));
				}
				listOfLit = or(listOfLit, lit);
			}
			return (listOfLit);
		} else if (!e.getSource().isConstant()) {
			// println ("contains branch 2");
			// println ("[contains] source not constant");
			BVExpr source = getBVExpr(e.getSource());
			String destCons = e.getDest().getSolution();
			int diff = e.getSource().getLength() - destCons.length();
			// println ("[contains] diff: " + diff);
			BVExpr listOfLit = null;
			for (int i = 0; i <= diff; i++) {
				BVExpr lit = null;
				for (int j = i; j < i + destCons.length(); j++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - j) * 8 - 1,
							(e.getSource().getLength() - j) * 8 - 8);
					BVExpr cons = new BVConst(destCons.charAt(j - i));
					lit = and(lit, new BVEq(sourceTemp, cons));
				}
				listOfLit = or(listOfLit, lit);
			}
			return (listOfLit);
		} else if (!e.getDest().isConstant()) {
			// println ("contains branch 3");
			BVExpr dest = getBVExpr(e.getDest());
			String sourceCons = e.getSource().getSolution();
			String[] possibleSolutions = new String[e.getSource().getLength() - e.getDest().getLength() + 1];
			for (int i = 0; i <= e.getSource().getLength() - e.getDest().getLength(); i++) {
				possibleSolutions[i] = sourceCons.substring(i, i + e.getDest().getLength());
			}
			BVExpr listOfLit = null;
			for (String s : possibleSolutions) {
				BVExpr lit = null;
				for (int i = 0; i < s.length(); i++) {
					BVExpr temp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
							(e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(sourceCons.charAt(i));
					lit = and(lit, new BVEq(temp, cons));
				}
				listOfLit = or(listOfLit, lit);
			}
			return (listOfLit);
		} else {
			String constant1 = e.getSource().getSolution();
			String constant2 = e.getDest().getSolution();
			if (constant1.contains(constant2)) {
				return new BVTrue();
			} else {
				return new BVFalse();
			}
		}
		// println ("contains no branch");
		// return null;
	}

	private static void handleEdgeContains(EdgeContains e) {
		if (e.getSource().getLength() == e.getDest().getLength()) {
			// println ("[handleEdgeContains] handing over to equals");
			post(equal(e));
			return;
		}
		post(contains(e));
	}

	private static void handleEdgeIndexOf2(EdgeIndexOf2 e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				BVExpr lit = null;
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - (i - index)) * 8 - 1,
							(e.getDest().getLength() - (i - index)) * 8 - 8);
					lit = and(lit, new BVEq(sourceTemp, destTemp));
				}
				post(lit);
			} else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				} else if (e.getSource().getLength() == e.getDest().getLength()) {
					post(new BVNot(equal(e)));
					return;
				} else {
					post(new BVNot(contains(e))); // TODO: fix this, it should
													// take into account the
													// minimal distance
				}
			}
		} else if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			String destCons = e.getDest().getSolution();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				BVExpr lit = null;
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(destCons.charAt(i - index));
					lit = and(lit, new BVEq(sourceTemp, cons));
				}
				post(lit);
			} else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				} else if (e.getSource().getLength() == e.getDest().getLength()) {
					post(new BVNot(equal(e)));
					return;
				} else {
					post(new BVNot(contains(e)));
				}
			}
		} else if (!e.getDest().isConstant()) {
			String sourceCons = e.getSource().getSolution();

			BVExpr dest = getBVExpr(e.getDest());
			int index = e.getIndex().solutionInt();

			if (index > -1) {
				String realSolution = sourceCons.substring(index, index + e.getDest().getLength());
				BVExpr lit = null;
				for (int i = 0; i < realSolution.length(); i++) {
					BVExpr destExpr = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
							(e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(realSolution.charAt(i));
					lit = and(lit, new BVEq(destExpr, cons));
				}
				post(lit);
			} else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				} else if (e.getSource().getLength() == e.getDest().getLength()) {
					post(new BVNot(equal(e)));
					return;
				} else {
					post(new BVNot(contains(e)));
				}
			}
		}
	}

	private static void handleEdgeIndexOf(EdgeIndexOf e) {
		// println ("[handleEdgeIndexOf]");
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			// println ("branch 1");
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				// println ("branch 1.1, index: " + index);
				BVExpr totalLit = null;
				// println ("e.getDest().getLength(): " +
				// e.getDest().getLength());
				for (int i = 0; i <= index - e.getDest().getLength(); i++) {
					BVExpr lit = null;
					for (int j = 0; j < e.getDest().getLength(); j++) {
						int totalOffset = i + j;
						BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - totalOffset) * 8 - 1,
								(e.getSource().getLength() - totalOffset) * 8 - 8);
						BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - j) * 8 - 1,
								(e.getDest().getLength() - j) * 8 - 8);
						lit = and(lit, new BVEq(sourceTemp, destTemp));
					}
					totalLit = and(totalLit, new BVNot(lit));
				}
				// println ("totalLit: " + totalLit);
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - (i - index)) * 8 - 1,
							(e.getDest().getLength() - (i - index)) * 8 - 8);
					totalLit = and(totalLit, new BVEq(sourceTemp, destTemp));
				}
				post(totalLit);
			} else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				} else if (e.getSource().getLength() == e.getDest().getLength()) {
					post(new BVNot(equal(e)));
					return;
				} else {
					post(new BVNot(contains(e)));
				}
			}
		} else if (!e.getSource().isConstant()) {
			// println ("branch 2");
			BVExpr source = getBVExpr(e.getSource());
			String destCons = e.getDest().getSolution();
			int index = e.getIndex().solutionInt();
			if (index > -1) {
				// println ("branch 2.1");
				BVExpr totalLit = null;
				// Characters before should not be equal
				for (int i = 0; i <= index - destCons.length(); i++) { // TODO:
																		// Double
																		// check
					BVExpr lit = null;
					for (int j = 0; j < destCons.length(); j++) {
						int entireOff = i + j;
						BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - entireOff) * 8 - 1,
								(e.getSource().getLength() - entireOff) * 8 - 8);
						BVExpr cons = new BVConst(destCons.charAt(j));
						lit = and(lit, new BVEq(sourceTemp, cons));
					}
					totalLit = and(totalLit, new BVNot(lit));
				}
				for (int i = index; i < index + e.getDest().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(destCons.charAt(i - index));
					totalLit = and(totalLit, new BVEq(sourceTemp, cons));
				}
				post(totalLit);
			} else {
				// println ("branch 2.2");
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				} else if (e.getSource().getLength() == e.getDest().getLength()) {
					post(new BVNot(equal(e)));
					return;
				} else {
					post(new BVNot(contains(e)));
				}
			}
		} else if (!e.getDest().isConstant()) {
			// println ("branch 3");
			String sourceCons = e.getSource().getSolution();

			BVExpr dest = getBVExpr(e.getDest());
			int index = e.getIndex().solutionInt();

			if (index > -1) {
				String realSolution = sourceCons.substring(index, index + e.getDest().getLength());
				BVExpr lit = null;
				for (int i = 0; i < realSolution.length(); i++) {
					BVExpr destExpr = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
							(e.getDest().getLength() - i) * 8 - 8);
					BVExpr cons = new BVConst(realSolution.charAt(i));
					lit = and(lit, new BVEq(destExpr, cons));
				}
				post(lit);
			} else {
				if (e.getSource().getLength() < e.getDest().getLength()) {
					return;
				} else if (e.getSource().getLength() == e.getDest().getLength()) {
					post(new BVNot(equal(e)));
					return;
				} else {
					post(new BVNot(contains(e)));
				}
			}
		}
	}

	private static void handleEdgeIndexOfChar(EdgeIndexOfChar e) {
		if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				BVExpr lit = null;
				/* no other occurences of the character may come before */
				for (int i = 0; i < index; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst(character);
					lit = and(lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1,
						(e.getSource().getLength() - index) * 8 - 8);
				BVExpr constant = new BVConst(character);
				lit = and(lit, new BVEq(sourceTemp, constant));
				post(lit);
				// println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			} else {
				BVExpr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst(character);
					lit = and(lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				post(lit);
			}
		} else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.indexOf(character);
			post(new BVEq(new BVConst(actualAns), new BVConst(index)));
		}
	}

	private static void handleEdgeLastIndexOfChar(EdgeLastIndexOfChar e) {
		if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				BVExpr lit = null;
				/* no other occurences of the character may come after */
				for (int i = index + 1; i < e.getSource().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst(character);
					lit = and(lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1,
						(e.getSource().getLength() - index) * 8 - 8);
				BVExpr constant = new BVConst(character);
				lit = and(lit, new BVEq(sourceTemp, constant));
				post(lit);
				// println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			} else {
				BVExpr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst(character);
					lit = and(lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				post(lit);
			}
		} else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.indexOf(character);
			post(new BVEq(new BVConst(actualAns), new BVConst(index)));
		}
	}

	private static void handleEdgeLastIndexOfChar2(EdgeLastIndexOfChar2 e) {
		if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				BVExpr lit = null;
				/*
				 * no other occurences of the character may come after up till
				 * second argument
				 */
				for (int i = index + 1; i < e.getIndex().getMinDist().solution(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst(character);
					lit = and(lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1,
						(e.getSource().getLength() - index) * 8 - 8);
				BVExpr constant = new BVConst(character);
				lit = and(lit, new BVEq(sourceTemp, constant));
				post(lit);
				// println ("[handleEdgeIndexOfChar] lit: " + lit.toString());
			} else {
				BVExpr lit = null;
				// Can not feature uptil the second argument
				for (int i = 0; i < e.getIndex().getMinDist().solution(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst(character);
					lit = and(lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				post(lit);
			}
		} else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.lastIndexOf(character, e.getIndex().getMinDist().solutionInt());
			post(new BVEq(new BVConst(actualAns), new BVConst(index)));
		}
	}

	private static void handleEdgeIndexOfChar2(EdgeIndexOfChar2 e) {
		if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			if (index > -1) {
				// println ("[handleEdgeIndexOfChar2] branch 1");
				BVExpr lit = null;
				/* no other occurences of the character may come before */
				// println ("[handleEdgeIndexOfChar2]
				// e.getIndex().getMinDist().solution() = " +
				// e.getIndex().getMinDist().solution());
				int i = e.getIndex().getMinDist().solutionInt();
				if (e.getIndex().getMinDist().solution() < 0) {
					i = 0;
				}
				for (; i < index; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst(character);
					lit = and(lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - index) * 8 - 1,
						(e.getSource().getLength() - index) * 8 - 8);
				BVExpr constant = new BVConst(character);
				lit = and(lit, new BVEq(sourceTemp, constant));
				post(lit);
			} else {
				BVExpr lit = null;
				for (int i = 0; i < e.getSource().getLength(); i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - i) * 8 - 1,
							(e.getSource().getLength() - i) * 8 - 8);
					BVExpr constant = new BVConst(character);
					lit = and(lit, new BVNot(new BVEq(sourceTemp, constant)));
				}
				post(lit);
			}
		} else {
			String source = e.getSource().getSolution();
			int index = e.getIndex().solutionInt();
			char character = (char) e.getIndex().getExpression().solution();
			int actualAns = source.indexOf(character, e.getIndex().getMinDist().solutionInt());
			post(new BVEq(new BVConst(actualAns), new BVConst(index)));
		}
	}

	private static void handleEdgeNotContains(EdgeNotContains e) {
		if (e.getSource().getLength() < e.getDest().getLength()) {
			return;
		}
		post(new BVNot(contains(e)));
	}

	private static void handleEdgeSubstring1Equal(EdgeSubstring1Equal e) {
		if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			BVExpr dest = getBVExpr(e.getDest());
			int arg1 = e.getArgument1();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1,
						(e.getSource().getLength() - (i + arg1)) * 8 - 8);
				BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
						(e.getDest().getLength() - i) * 8 - 8);
				lit = and(lit, new BVEq(sourceTemp, destTemp));
			}
			post(lit);
		} else if (!e.getSource().isConstant()) {
			BVExpr source = getBVExpr(e.getSource());
			String destCons = e.getDest().getSolution();
			int arg1 = e.getArgument1();
			BVExpr lit = null;
			for (int i = 0; i < e.getDest().getLength(); i++) {
				BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1,
						(e.getSource().getLength() - (i + arg1)) * 8 - 8);
				BVExpr destTemp = new BVConst(destCons.charAt(i));
				lit = and(lit, new BVEq(sourceTemp, destTemp));
			}
			post(lit);
		} else {
			throw new RuntimeException("Preprocessor should handle this");
		}
	}

	private static void handleEdgeSubstring2Equal(EdgeSubstring2Equal e) {
		if (!e.hasSymbolicArgs()) {
			if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				BVExpr source = getBVExpr(e.getSource());
				BVExpr dest = getBVExpr(e.getDest());
				int arg1 = e.getArgument1();
				int arg2 = e.getArgument2();
				BVExpr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1,
							(e.getSource().getLength() - (i + arg1)) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
							(e.getDest().getLength() - i) * 8 - 8);
					lit = and(lit, new BVEq(sourceTemp, destTemp));
				}
				post(lit);
			} else if (!e.getSource().isConstant()) {
				BVExpr source = getBVExpr(e.getSource());
				String destCons = e.getDest().getSolution();
				int arg1 = e.getArgument1();
				int arg2 = e.getArgument2();
				BVExpr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1,
							(e.getSource().getLength() - (i + arg1)) * 8 - 8);
					BVExpr destTemp = new BVConst(destCons.charAt(i));
					lit = and(lit, new BVEq(sourceTemp, destTemp));
				}
				post(lit);
			} else {
				throw new RuntimeException("Preprocessor should handle this");
			}
		} else if (e.getSymbolicArgument1() == null && e.getSymbolicArgument2() != null) {
			if (!e.getSource().isConstant() && !e.getDest().isConstant()) {
				BVExpr source = getBVExpr(e.getSource());
				BVExpr dest = getBVExpr(e.getDest());
				int arg1 = e.getArgument1();
				int arg2 = e.getSymbolicArgument2().solutionInt();
				BVExpr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1,
							(e.getSource().getLength() - (i + arg1)) * 8 - 8);
					BVExpr destTemp = new BVExtract(dest, (e.getDest().getLength() - i) * 8 - 1,
							(e.getDest().getLength() - i) * 8 - 8);
					lit = and(lit, new BVEq(sourceTemp, destTemp));
				}
				post(lit);
			} else if (!e.getSource().isConstant()) {
				BVExpr source = getBVExpr(e.getSource());
				String destCons = e.getDest().getSolution();
				int arg1 = e.getArgument1();
				int arg2 = e.getSymbolicArgument2().solutionInt();
				if (arg2 - arg1 != destCons.length()) {
					// TODO: Can definitly improve here
					// global_pc._addDet(Comparator.EQ,
					// e.getSymbolicArgument2(), destCons.length() + arg1);
					post(new BVFalse());
					return;
					// throw new RuntimeException((arg2 - arg1) + " is not equal
					// to '" + destCons + "' length of " + destCons.length());
				}
				BVExpr lit = null;
				for (int i = 0; i < arg2 - arg1; i++) {
					BVExpr sourceTemp = new BVExtract(source, (e.getSource().getLength() - (i + arg1)) * 8 - 1,
							(e.getSource().getLength() - (i + arg1)) * 8 - 8);
					BVExpr destTemp = new BVConst(destCons.charAt(i));
					lit = and(lit, new BVEq(sourceTemp, destTemp));
				}
				post(lit);
			} else {
				throw new RuntimeException("Preprocessor should handle this");
			}
		} else {
			throw new RuntimeException("not supported, yet");
		}
	}

	private static BVExpr and(BVExpr orig, BVExpr newE) {
		if (orig == null) {
			return newE;
		} else {
			return new BVAnd(orig, newE);
		}
	}

	private static BVExpr or(BVExpr orig, BVExpr newE) {
		if (orig == null) {
			return newE;
		} else {
			return new BVOr(orig, newE);
		}
	}

	private static void post(BVExpr e) {
		if (expr == null) {
			expr = e;
		} else {
			expr = new BVAnd(e, expr);
		}
	}

	private static boolean[] toBits(char c) {
		boolean[] result = new boolean[8];
		int num = (int) c;
		int i = result.length - 1;
		int div = 128;
		while (num > 0) {
			int temp = num / div;
			num = num - div * temp;
			div = div / 2;
			if (temp == 1)
				result[i] = true;
			i--;
		}
		return result;
	}

	private static BVExpr getBVExpr(Vertex v) {
		BVExpr result = map.get(v);
		if (result == null) {
			// 8 is easier
			// result = vc.varExpr("a", vc.arrayType(vc.intType(),
			// vc.intType()));
			result = new BVVar(v.getName(), 8 * v.getLength());
			// println ("[BVExpr] " + v.getName() + " length: " + (8 *
			// v.getLength()));
			map.put(v, result);
			// Apply character constraints to each character
			BVExpr lit = null;
			for (int i = 0; i < v.getLength(); i++) {
				BVExpr temp = new BVExtract(result, i * 8 + 7, i * 8);
				BVExpr cons1 = new BVLT(temp, new BVConst(SymbolicStringConstraintsGeneral.MAX_CHAR));
				BVExpr cons2 = new BVNot(new BVLT(temp, new BVConst(SymbolicStringConstraintsGeneral.MIN_CHAR)));
				if (lit == null) {
					lit = new BVAnd(cons1, cons2);
				} else {
					lit = new BVAnd(lit, new BVAnd(cons1, cons2));
				}
				if (v.isConstant()) {
					// the strings are stored in reverse in the bitvector
					String vertexString = v.getSolution();
					int charIndex = (vertexString.length() - 1) - i;
					char currentChar = vertexString.charAt(charIndex);
					BVEq consEq = new BVEq(temp, new BVConst(currentChar));
					lit = new BVAnd(lit, consEq);
				}
			}
			post(lit);
		}
		return result;
	}

	private static String getSMTLibString(Expr em) {
		StringBuilder sb = new StringBuilder();

		preOrderTraversal(em, sb);

		return sb.toString();
	}

	private static void preOrderTraversal(Expr em, StringBuilder string) {

		if (em.isAnd()) {
			string.append("and");
		} else if (em.isOr()) {
			string.append("or");
		} else if (em.isNot()) {
			string.append("not");
		} else if (em.isEq()) {
			string.append("=");
		} else if (em.isBvExtract()) {
			string.append("BV Extract");
			return;
		} else {
			string.append("|" + em.getKind() + "|");
		}
		string.append(" ");

		string.append("(");
		for (Object e : em.getChildren()) {
			preOrderTraversal((Expr) e, string);
		}
		string.append(")");
	}

	private static String getSMTLibMsg() {
		StringBuilder sb = new StringBuilder();

		for (Entry<Vertex, BVExpr> e : map.entrySet()) {
			BVVar var = (BVVar) e.getValue();
			sb.append(var.toSMTLibDec());
			sb.append("\n");
		}

		sb.append("(assert ");
		sb.append(expr.toSMTLib());
		sb.append(")\n");

		sb.append("(check-sat)\n(get-info model)\n");

		return sb.toString();
	}

}

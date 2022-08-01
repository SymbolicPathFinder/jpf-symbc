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

package gov.nasa.jpf.symbc.string.testing;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.List;
import java.util.Random;
import java.util.Scanner;
import java.util.Timer;

import javax.print.attribute.IntegerSyntax;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.symbc.string.SymbolicIndexOf2Integer;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfChar2Integer;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfCharInteger;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfInteger;
import gov.nasa.jpf.symbc.string.SymbolicIntegerGenerator;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOf2Integer;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOfChar2Integer;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOfCharInteger;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOfInteger;
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;
import gov.nasa.jpf.symbc.string.SymbolicStringTimeOut;
import gov.nasa.jpf.symbc.string.SymbolicStringTimedOutException;
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
import gov.nasa.jpf.symbc.string.translate.BVVar;
import gov.nasa.jpf.symbc.string.translate.TranslateToAutomata;
import gov.nasa.jpf.symbc.string.translate.TranslateToAutomata2;
import gov.nasa.jpf.symbc.string.translate.TranslateToZ3;
import gov.nasa.jpf.symbc.string.translate.TranslateToZ3Inc;

public class RandomTest {
	
	static int totalWeight;
	static SymbolicIntegerGenerator sig;
	static Random random;
	static int counter;
	static PathCondition pc;
	
	private static final String Z3_Inc = "Z3 Inc";
	private static final String Z3 = "Z3";
	private static final String Automata = "Automata";
	private static IntegerConstant integerCons[];
	private static SymbolicInteger integerVars[];
	private static int vertexCounter;
	
	private static int TEST_TIMEOUT = 120 * 1000; //(ms)
	
	public static Profile get3smallSetOfEdges() {
		Profile p = Profile.NewProfile();
		p.amountOfStringCons = 5;
		p.stringConsMaxLength = 5;
		p.amountOfStringVar = 2;
		p.amountOfEdges = 3;
		p.amountOfIntegerCons = 2;
		p.amountOfIntegerVar = 2;
		p.listOfEdgesToBeUsed = Profile.smallSetOfEdges();
		return p;
	}
	
	public static Profile get3defaultSetOfEdges() {
		Profile p = Profile.NewProfile();
		p.amountOfStringCons = 5;
		p.stringConsMaxLength = 5;
		p.amountOfStringVar = 2;
		p.amountOfEdges = 3;
		p.amountOfIntegerCons = 2;
		p.amountOfIntegerVar = 2;
		p.listOfEdgesToBeUsed = Profile.defaultSetOfEdges2();
		return p;
	}
	
	public static Profile get3goodSetOfEdges() {
		Profile p = Profile.NewProfile();
		p.amountOfStringCons = 5;
		p.stringConsMaxLength = 5;
		p.amountOfStringVar = 2;
		p.amountOfEdges = 3;
		p.amountOfIntegerCons = 2;
		p.amountOfIntegerVar = 2;
		p.listOfEdgesToBeUsed = Profile.defaultGoodOfEdges2();
		return p;
	}
	
	public static void main (String [] args) throws NumberFormatException, IOException {
		setUpJPF();
		
		//Profile p = get3smallSetOfEdges();
		Profile p = get3goodSetOfEdges();
		
		boolean showOnlyGraph = false;
		boolean extraDetail = true;
		
		//args = new String[]{"4482676770472428340"};
		//args = new String[]{"7463434583100419681"};
		//args = new String[]{"6195941135273736924"};
		//args = new String[]{"-5452898171472999736"};
		//args = new String[]{"-8789835043277711195"};
		//args = new String[]{"-8333472512654717307"};
		//TODO: 2797260435590869202
		//args = new String[]{"8916679733395261340"};
		//args = new String[]{"-6073284858942019344"};
		//args = new String[]{"3068802442326409421"};
		//args = new String[]{"4058543832693410397"};
		//args = new String[]{"945342098152955059"};
		//args = new String[]{"5296771593399017434"};
		//args = new String[]{"2060370656708903858"};
		//args = new String[]{"8047697279252921453"};
		//args = new String[]{"4245195189447030174"};
		//args = new String[]{"-7189896289378272226"};
		//args = new String[]{"-3605963236366167326"};
		//args = new String[]{"-7236756415893867232"};
		//args = new String[]{"7027824590206899706"};
		//args = new String[]{"-4376207953586733395"};
		//args = new String[]{"6208297289381565893"};
		//args = new String[]{"8607490714217974499"};
		//args = new String[]{"-9113673849729818348"};
		//args = new String[]{"705452481494713414"}; good diff
		//args = new String[]{"-1242344884180004662"};
		//args = new String[]{ "3476996485065834879"};
		//args = new String[]{"-v", "/home/gideon/numbers"};
		//args = new String[]{"7049847513125521827"};
		//args = new String[]{"8911160557294150329"};
		//args = new String[]{"-8564134299976833108"};
		//args = new String[]{"-2483205023141871181"};
		//args = new String[]{"1900680547994741596"};
		//args = new String[]{"-3575625896976452488"};
		args = new String[]{"-848008875103978746"};
		if (args.length == 0) {
			System.out.println("[data]," + p);
			for (int i = 0; i < 1000; i++) {
				random = new Random();
				long seed = random.nextLong();
				System.out.println("Starting: " + seed);
				Result z3dur = go (p, seed, Z3_Inc);
				Result autodur = go (p, seed, Automata);
				System.out.println("[data],\""+seed+"\","+z3dur.time+","+autodur.time);
				
			}
		}
		else if (args.length == 1) {
			random = new Random();
			long seed = Long.parseLong(args[0]);
			StringGraph sg = generateRandomStringGraph (p, seed);
			System.out.println(sg.toDot());
			if (showOnlyGraph == false) {
				System.out.println("[RandomTest] Calling with z3");
				Result z3dur = go (p, seed, Z3_Inc);
				System.out.println("[RandomTest] Calling with automata");
				Result autodur = go (p, seed, Automata);
				System.out.print("[data],\""+seed+"\","+z3dur.time+","+autodur.time);
				if (extraDetail == true) {
					System.out.print(","+z3dur.result+","+autodur.result);
				}
				System.out.println();
			}
		}
		else {
		  BufferedReader br = new BufferedReader(new FileReader(args[1]));
			String number;
			while ((number = br.readLine()) != null) {
				long seed = Long.parseLong(number);
				random = new Random();
				StringGraph sg = generateRandomStringGraph (p, seed);
				System.out.println(seed + "\n" + sg.toDot());
				random = new Random();
				System.out.println("[RandomTest] Calling with z3");
				Result z3dur = go (p, seed, Z3_Inc);
				System.out.println("[RandomTest] Calling with automata");
				Result autodur = go (p, seed, Automata);
				System.out.print("[data]");
				if (z3dur.time > 0 && autodur.time > 0) {
					if (z3dur.result != autodur.result) {
						System.out.print("[FAILURE]");
					}
				}
				System.out.println(",\""+seed+"\","+z3dur.time+","+autodur.time);
			}
			br.close();
		}
	}
	
	public static Result go (Profile p, long seed, String Solver) {
		StringGraph sg = generateRandomStringGraph (p, seed);
		System.out.println(sg.toDot());
		boolean result = PreProcessGraph.preprocess(sg, pc);
		//System.out.println(sg.toDot());
		System.out.println(pc.header);
		System.out.println("Preprocessor " + result);
		if (result == false) {}
		else {
			long time = System.currentTimeMillis();
			if (Solver.equals (Z3_Inc)) {
				System.out.println("[RandomTest] branch 1");
				SymbolicStringConstraintsGeneral.TIMEOUT = TEST_TIMEOUT;
				SymbolicStringConstraintsGeneral.timedOut = false;
				SymbolicStringConstraintsGeneral.timer = new Timer();
				SymbolicStringConstraintsGeneral.timer.schedule(new SymbolicStringTimeOut(), SymbolicStringConstraintsGeneral.TIMEOUT);
				try {
					System.out.println("[RandomTest] Z3 inc staring");
					result = TranslateToZ3Inc.isSat(sg, pc);
					System.out.println("[RandomTest] Z3 inc done");
				} catch (SymbolicStringTimedOutException e) {
					SymbolicStringConstraintsGeneral.timer.cancel();
					return new Result(-2, false);
				}
				SymbolicStringConstraintsGeneral.timer.cancel();
			}
			else if (Solver.equals(Automata)) {
				System.out.println("[RandomTest] branch 2");
				SymbolicStringConstraintsGeneral.TIMEOUT = TEST_TIMEOUT;
				SymbolicStringConstraintsGeneral.timedOut = false;
				SymbolicStringConstraintsGeneral.timer = new Timer();
				SymbolicStringConstraintsGeneral.timer.schedule(new SymbolicStringTimeOut(), SymbolicStringConstraintsGeneral.TIMEOUT);
				try {
					result = TranslateToAutomata2.isSat(sg, pc);
					System.out.println("[RandomTest] Automata done");
				} catch (SymbolicStringTimedOutException e) {
					SymbolicStringConstraintsGeneral.timer.cancel();
					return new Result (-2, false);
				}
				SymbolicStringConstraintsGeneral.timer.cancel();
			}
			long dur = System.currentTimeMillis() - time;
			//System.out.println("[output] " + Solver + ": " + dur);
			return new Result(dur, result);
		}
		return new Result(-1, false);
	}
	
	public static void setUpJPF () {
		Config cfg = new Config(new String[]{""});
		new SymbolicInstructionFactory(cfg);
	}
	
	public static StringGraph generateRandomStringGraph (Profile p, long seed) {
		StringGraph result = new StringGraph();
		pc = new PathCondition();
		//System.out.println("Random seed: " + seed);
		random.setSeed(seed);
		counter = 0;
		
		integerCons = new IntegerConstant[p.amountOfIntegerCons];
		integerVars = new SymbolicInteger[p.amountOfIntegerVar];
		
		totalWeight = 0;
		for (int i = 0; i < p.listOfEdgesToBeUsed.length; i++) {
			totalWeight = totalWeight + p.listOfEdgesToBeUsed[i];
		}
		
		vertexCounter = 0;
		
		sig = new SymbolicIntegerGenerator();
		char character = 'a';
		
		for (int i = 0; i < p.amountOfStringVar; i++) {
			result.addVertex(new Vertex("SYM_" + String.valueOf(character), sig));
			character = (char) ((int) character + 1);
		}
		
		for (int i = 0; i < p.amountOfStringCons; i++) {
			String name = getRandomConstantString (random.nextInt(p.stringConsMaxLength) + 1);
			result.addVertex(new Vertex("CONST_" + name, name, true));
		}
		
		for (int i = 0; i < p.amountOfIntegerCons; i++) {
			integerCons[i] = new IntegerConstant(random.nextInt(200));
		}
		
		for (int i = 0; i < p.amountOfIntegerVar; i++) {
			integerVars[i] = new SymbolicInteger("SYM_INT_" + i);
		}
		
		for (int i = 0; i < p.amountOfEdges; i++ ) {
			double ran = random.nextDouble();
			ran = ran * totalWeight;
			ran = Math.round (ran);
			int index = getIndex ((int) ran, p.listOfEdgesToBeUsed);
			switch (index) {
			case 0:
				//EdgeCharAt
				handleEdgeCharAt(result, random.nextInt(4));
				break;
			case 1:
				//EdgeConcat
				handleEdgeConcat(result);
				break;
			case 2:
				//EdgeContains
				handleEdgeContains (result);
				break;
			case 3:
				//EdgeEndsWith
				handleEdgeEndsWith (result);
				break;
			case 4:
				//EdgeEqual
				handleEdgeEqual (result);
				break;
			case 5:
				//EdgeIndexOf
				handleEdgeIndexOf (result, random.nextInt(2));
				break;
			case 6:
				//EdgeIndexOf2
				handleEdgeIndexOf2 (result, random.nextInt(4));
				break;
			case 7:
				//EdgeIndexOfChar
				handleEdgeIndexOfChar (result, random.nextInt(2));
				break;
			case 8:
				//EdgeIndexOfChar2
				handleEdgeIndexOfChar2 (result, random.nextInt(8));
				break;
			case 9:
				//EdgeLastIndexOf
				handleEdgeLastIndexOf (result, random.nextInt(2));
				break;
			case 10:
				//EdgeLastIndexOf2
				handleEdgeLastIndexOf2 (result, random.nextInt(4));
				break;
			case 11:
				//EdgeLastIndexOfChar
				handleEdgeLastIndexOfChar (result, random.nextInt(2));
				break;
			case 12:
				//EdgeLastIndexOfChar2
				handleEdgeLastIndexOfChar2 (result, random.nextInt(8));
				break;
			case 13:
				//EdgeNotContains
				handleEdgeNotContains (result);
				break;
			case 14:
				//EdgeNotEndsWith
				handleEdgeNotEndsWith (result);
				break;
			case 15:
				//EdgeNotEquals
				handleEdgeNotEquals (result);
				break;
			case 16:
				//EdgeNotStartsWith
				handleEdgeNotStartsWith (result);
				break;
			case 17:
				//EdgeReplaceCharChar
				throw new RuntimeException ("Not implemented yet");
			case 18:
				//EdgeStartsWith
				handleEdgeStartsWith (result);
				break;
			case 19:
				//EdgeSubstring1Equal
				handleEdgeSubstring1Equal(result);
				break;
			case 20:
				//EdgeSubstring2Equal
				handleEdgeSubstring2Equal(result, random.nextInt(2));
				break;
			case 21:
				//EdgeTrimEqual
				handleEdgeTrimEqual(result);
				break;
			}
		}
		
		return result;
	}
	
	private static void handleEdgeTrimEqual (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2)) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeTrimEqual edge = new EdgeTrimEqual("EdgeTrimEqual_" + getCounter(), v1, v2);
	}
	
	private static void handleEdgeSubstring1Equal (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2)) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		IntegerConstant ic = randomConsInteger();
		pc._addDet(Comparator.GE, ic, 1);
		pc._addDet(Comparator.LE, ic, PreProcessGraph.MAXIMUM_LENGTH);
		if (v1.isConstant()) {
			pc._addDet(Comparator.LE, ic, v1.getLength());
		} else {
			pc._addDet(Comparator.LE, ic, v1.getSymbolicLength());
		}
		/*println (pc.header.toString());
		println ("ic: " + ic);*/
		EdgeSubstring1Equal edge = new EdgeSubstring1Equal("EdgeSubstring1Equal_" + getCounter(), ic.solutionInt(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeSubstring2Equal (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2)) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		IntegerExpression ie1, ie2;
		System.out.println("mode: " + mode);
		switch (mode) {
		case 0:
			ie1 = randomConsInteger();
			ie2 = randomConsInteger();
			break;
		/*case 1:
			ie1 = randomSymInteger();
			ie2 = randomConsInteger();
			break;*/
		case 1:
			ie1 = randomConsInteger();
			ie2 = randomSymInteger();
			break;
		default:
			throw new RuntimeException("should not be reached");
		}
		//TDOD: Should maybe change
		EdgeSubstring2Equal edge = null;
		pc._addDet(Comparator.GE, ie1, 1);
		pc._addDet(Comparator.GE, ie2, 1);
		pc._addDet(Comparator.LE, ie1, PreProcessGraph.MAXIMUM_LENGTH);
		pc._addDet(Comparator.LE, ie2, PreProcessGraph.MAXIMUM_LENGTH);
		pc._addDet(Comparator.LE, ie1, ie2);
		if (!v2.isConstant()) {
			pc._addDet(Comparator.EQ, ie2._minus(ie1)._plus(1), v2.getSymbolicLength());
		} else {
			pc._addDet(Comparator.EQ, ie2._minus(ie1)._plus(1), v2.getLength());
		}
		if (v1.isConstant()) {
			pc._addDet(Comparator.LE, ie2, v1.getLength());
		}
		else {
			pc._addDet(Comparator.LE, ie2, v1.getSymbolicLength());
		}
		if (ie1 instanceof IntegerConstant && ie2 instanceof IntegerConstant) {
			edge = new EdgeSubstring2Equal("EdgeSubstring1Equal_" + getCounter(), ie1.solutionInt(), ie2.solutionInt(), v1, v2);
		}
		else if (ie1 instanceof IntegerConstant) {
			edge = new EdgeSubstring2Equal("EdgeSubstring1Equal_" + getCounter(), ie1.solutionInt(), ie2, v1, v2);
		}
		else if (ie2 instanceof IntegerConstant) {
			edge = new EdgeSubstring2Equal("EdgeSubstring1Equal_" + getCounter(), ie1, ie2.solutionInt(), v1, v2);
		}
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeIndexOf (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2)) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		IntegerExpression ie;
		switch (mode) {
		case 0:
			ie = randomConsInteger();
			break;
		case 1:
			ie = randomSymInteger();
			break;
		default:
			throw new RuntimeException("should not be reached");
		}
		SymbolicIndexOfInteger sioi = new SymbolicIndexOfInteger("TEMP_" + vertexCounter, 1, 30, null, null);
		vertexCounter++;
		pc._addDet(Comparator.EQ, ie, sioi);
		EdgeIndexOf edge = new EdgeIndexOf("EdgeIndexOf_" + getCounter(), v1, v2, sioi);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeLastIndexOf (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2)) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		IntegerExpression ie;
		switch (mode) {
		case 0:
			ie = randomConsInteger();
			break;
		case 1:
			ie = randomSymInteger();
			break;
		default:
			throw new RuntimeException("should not be reached");
		}
		SymbolicLastIndexOfInteger sioi = new SymbolicLastIndexOfInteger("TEMP_" + vertexCounter, 1, 30, null, null);
		vertexCounter++;
		pc._addDet(Comparator.EQ, ie, sioi);
		EdgeLastIndexOf edge = new EdgeLastIndexOf("EdgeLastIndexOf_" + getCounter(), v1, v2, sioi);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeIndexOfChar (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = new Vertex ("TEMP_" + vertexCounter, 1);
		vertexCounter++;
		IntegerExpression ie1, ie2;
		switch (mode) {
		case 0:
			ie1 = randomConsInteger();
			ie2 = randomConsInteger();
			break;
		case 1:
			ie1 = randomSymInteger();
			ie2 = randomConsInteger();
			break;
		case 2:
			ie1 = randomConsInteger();
			ie2 = randomSymInteger();
			break;
		case 3:
			ie1 = randomSymInteger();
			ie2 = randomSymInteger();
			break;
		default:
			throw new RuntimeException("should not be reached");
		}
		SymbolicIndexOfCharInteger sioi = new SymbolicIndexOfCharInteger("TEMP_" + vertexCounter, 1, 30, null, ie1);
		pc._addDet(Comparator.GE, ie1, SymbolicStringConstraintsGeneral.MIN_CHAR);
		pc._addDet(Comparator.LE, ie1, SymbolicStringConstraintsGeneral.MAX_CHAR);
		vertexCounter++;
		pc._addDet(Comparator.EQ, ie2, sioi);
		EdgeIndexOfChar edge = new EdgeIndexOfChar("EdgeIndexOfChar_" + getCounter(), v1, v2, sioi);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeLastIndexOfChar (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = new Vertex ("TEMP_" + vertexCounter, 1);
		vertexCounter++;
		IntegerExpression ie1, ie2;
		switch (mode) {
		case 0:
			ie1 = randomConsInteger();
			ie2 = randomConsInteger();
			break;
		case 1:
			ie1 = randomSymInteger();
			ie2 = randomConsInteger();
			break;
		case 2:
			ie1 = randomConsInteger();
			ie2 = randomSymInteger();
			break;
		case 3:
			ie1 = randomSymInteger();
			ie2 = randomSymInteger();
			break;
		default:
			throw new RuntimeException("should not be reached");
		}
		SymbolicLastIndexOfCharInteger sioi = new SymbolicLastIndexOfCharInteger("TEMP_" + vertexCounter, 1, 30, null, ie1);
		pc._addDet(Comparator.GE, ie1, SymbolicStringConstraintsGeneral.MIN_CHAR);
		pc._addDet(Comparator.LE, ie1, SymbolicStringConstraintsGeneral.MAX_CHAR);
		vertexCounter++;
		pc._addDet(Comparator.EQ, ie2, sioi);
		EdgeLastIndexOfChar edge = new EdgeLastIndexOfChar("EdgeLastIndexOfChar_" + getCounter(), v1, v2, sioi);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeIndexOfChar2 (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = new Vertex ("TEMP_" + vertexCounter, 1);
		vertexCounter++;
		IntegerExpression ie1, ie2,ie3;
		switch (mode) {
		case 0:
			ie1 = randomConsInteger();
			ie2 = randomConsInteger();
			ie3 = randomConsInteger();
			break;
		case 1:
			ie1 = randomSymInteger();
			ie2 = randomConsInteger();
			ie3 = randomConsInteger();
			break;
		case 2:
			ie1 = randomConsInteger();
			ie2 = randomSymInteger();
			ie3 = randomConsInteger();
			break;
		case 3:
			ie1 = randomSymInteger();
			ie2 = randomSymInteger();
			ie3 = randomConsInteger();
			break;
		case 4:
			ie1 = randomConsInteger();
			ie2 = randomConsInteger();
			ie3 = randomSymInteger();
			break;
		case 5:
			ie1 = randomSymInteger();
			ie2 = randomConsInteger();
			ie3 = randomSymInteger();
			break;
		case 6:
			ie1 = randomConsInteger();
			ie2 = randomSymInteger();
			ie3 = randomSymInteger();
			break;
		case 7:
			ie1 = randomSymInteger();
			ie2 = randomSymInteger();
			ie3 = randomSymInteger();
			break;	
		default:
			throw new RuntimeException("should not be reached");
		}
		/*System.out.println("ie1: " + ie1);
		System.out.println("ie2: " + ie2);
		System.out.println("ie3: " + ie3);*/
		SymbolicIndexOfChar2Integer sioi = new SymbolicIndexOfChar2Integer("TEMP_" + vertexCounter, 1, 30, null, ie1,ie3);
		pc._addDet(Comparator.GE, ie1, SymbolicStringConstraintsGeneral.MIN_CHAR);
		pc._addDet(Comparator.LE, ie1, SymbolicStringConstraintsGeneral.MAX_CHAR);
		vertexCounter++;
		pc._addDet(Comparator.EQ, ie2, sioi);
		pc._addDet(Comparator.GE, sioi, ie3);
		pc._addDet(Comparator.GE, ie3, 0);
		EdgeIndexOfChar2 edge = new EdgeIndexOfChar2("EdgeIndexOfChar_" + getCounter(), v1, v2, sioi);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeLastIndexOfChar2 (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = new Vertex ("TEMP_" + vertexCounter, 1);
		vertexCounter++;
		IntegerExpression ie1, ie2,ie3;
		switch (mode) {
		case 0:
			ie1 = randomConsInteger();
			ie2 = randomConsInteger();
			ie3 = randomConsInteger();
			break;
		case 1:
			ie1 = randomSymInteger();
			ie2 = randomConsInteger();
			ie3 = randomConsInteger();
			break;
		case 2:
			ie1 = randomConsInteger();
			ie2 = randomSymInteger();
			ie3 = randomConsInteger();
			break;
		case 3:
			ie1 = randomSymInteger();
			ie2 = randomSymInteger();
			ie3 = randomConsInteger();
			break;
		case 4:
			ie1 = randomConsInteger();
			ie2 = randomConsInteger();
			ie3 = randomSymInteger();
			break;
		case 5:
			ie1 = randomSymInteger();
			ie2 = randomConsInteger();
			ie3 = randomSymInteger();
			break;
		case 6:
			ie1 = randomConsInteger();
			ie2 = randomSymInteger();
			ie3 = randomSymInteger();
			break;
		case 7:
			ie1 = randomSymInteger();
			ie2 = randomSymInteger();
			ie3 = randomSymInteger();
			break;	
		default:
			throw new RuntimeException("should not be reached");
		}
		SymbolicLastIndexOfChar2Integer sioi = new SymbolicLastIndexOfChar2Integer("TEMP_" + vertexCounter, 1, 30, null, ie1,ie3);
		pc._addDet(Comparator.GE, ie1, SymbolicStringConstraintsGeneral.MIN_CHAR);
		pc._addDet(Comparator.LE, ie1, SymbolicStringConstraintsGeneral.MAX_CHAR);
		vertexCounter++;
		pc._addDet(Comparator.EQ, ie2, sioi);
		EdgeLastIndexOfChar2 edge = new EdgeLastIndexOfChar2("EdgeLastIndexOfChar2_" + getCounter(), v1, v2, sioi);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeIndexOf2 (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2)) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		IntegerExpression ie1, ie2;
		switch (mode) {
		case 0:
			ie1 = randomConsInteger();
			ie2 = randomConsInteger();
			break;
		case 1:
			ie1 = randomSymInteger();
			ie2 = randomConsInteger();
			break;
		case 2:
			ie1 = randomConsInteger();
			ie2 = randomSymInteger();
			break;
		case 3:
			ie1 = randomSymInteger();
			ie2 = randomSymInteger();
			break;
		default:
			throw new RuntimeException("should not be reached");
		}
		SymbolicIndexOf2Integer sioi = new SymbolicIndexOf2Integer("TEMP_" + vertexCounter, 1, 30, null, null, ie1);
		vertexCounter++;
		pc._addDet(Comparator.EQ, ie2, sioi);
		EdgeIndexOf2 edge = new EdgeIndexOf2("EdgeIndexOf2_" + getCounter(), v1, v2, sioi);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeLastIndexOf2 (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2)) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		IntegerExpression ie1, ie2;
		switch (mode) {
		case 0:
			ie1 = randomConsInteger();
			ie2 = randomConsInteger();
			break;
		case 1:
			ie1 = randomSymInteger();
			ie2 = randomConsInteger();
			break;
		case 2:
			ie1 = randomConsInteger();
			ie2 = randomSymInteger();
			break;
		case 3:
			ie1 = randomSymInteger();
			ie2 = randomSymInteger();
			break;
		default:
			throw new RuntimeException("should not be reached");
		}
		SymbolicLastIndexOf2Integer sioi = new SymbolicLastIndexOf2Integer("TEMP_" + vertexCounter, 1, 30, null, null, ie1);
		vertexCounter++;
		pc._addDet(Comparator.EQ, ie2, sioi);
		EdgeLastIndexOf2 edge = new EdgeLastIndexOf2("EdgeLastIndexOf2_" + getCounter(), v1, v2, sioi);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeCharAt (StringGraph result, int mode) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = new Vertex ("TEMP_" + vertexCounter, 1);
		vertexCounter++;
		IntegerExpression i1, i2;
		switch (mode) {
		case 0:
			i1 = randomConsInteger ();
			i2 = randomConsInteger ();
			break;
		case 1:
			i1 = randomConsInteger();
			i2 = randomSymInteger();
			break;
		case 2:
			i1 = randomSymInteger();
			i2 = randomConsInteger();
			break;
		case 3:
			i1 = randomSymInteger();
			i2 = randomSymInteger();
			break;
		default:
			throw new RuntimeException ("Should not be reached");
		}
		EdgeCharAt edge = new EdgeCharAt("EdgeCharAt_" + getCounter(), v1, v2, i1, i2);
		pc._addDet(Comparator.GE, i2, SymbolicStringConstraintsGeneral.MIN_CHAR);
		pc._addDet(Comparator.LE, i2, SymbolicStringConstraintsGeneral.MAX_CHAR);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeConcat (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		Vertex v3 = selectRandomVertex(result);
		while (v1.equals(v2) || v1.equals(v3) || v2.equals(v3)) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
			v3 = selectRandomVertex(result);
		}
		EdgeConcat edge = new EdgeConcat("EdgeConcat_" + getCounter(), v1, v2, v3);
		result.addEdge(v1,v2,v3,edge);
	}
	
	private static IntegerConstant randomConsInteger () {
		return integerCons[random.nextInt(integerCons.length)];
	}
	
	private static SymbolicInteger randomSymInteger () {
		return integerVars[random.nextInt(integerVars.length)];
	}
	
	private static void handleEdgeStartsWith (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeStartsWith edge = new EdgeStartsWith("EdgeStartsWith_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
		
	private static void handleEdgeNotEquals (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		//TODO: Investigate
		if (v2.isConstant()) {
			pc._addDet(Comparator.GE, v1.getSymbolicLength(), v2.getLength());
		}
		EdgeNotEqual edge = new EdgeNotEqual("EdgeNotEqual_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeNotStartsWith (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		//TODO: Investigate
		if (v2.isConstant()) {
			pc._addDet(Comparator.GE, v1.getSymbolicLength(), v2.getLength());
		}
		EdgeNotStartsWith edge = new EdgeNotStartsWith("EdgeNotStartsWith_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeNotEndsWith (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		//TODO: Investigate
		if (v2.isConstant()) {
			pc._addDet(Comparator.GE, v1.getSymbolicLength(), v2.getLength());
		}
		EdgeNotEndsWith edge = new EdgeNotEndsWith("EdgeNotEndsWith_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeNotContains (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeNotContains edge = new EdgeNotContains("EdgeNotContains_" + getCounter(), v1, v2);
		//TODO: Investigate
		if (v2.isConstant()) {
			pc._addDet(Comparator.GE, v1.getSymbolicLength(), v2.getLength());
		}
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeEqual (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeEqual edge = new EdgeEqual("EdgeEqual_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeEndsWith (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeEndsWith edge = new EdgeEndsWith("EdgeEndsWith_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeContains (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeContains edge = new EdgeContains("EdgeContains_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static int getCounter () {
		int oldcount = counter;
		counter++;
		return oldcount;
	}
	
	private static Vertex selectRandomVertex (StringGraph g) {
		List<Vertex> vertecis = g.getVertices();
		int ranIndex = random.nextInt(vertecis.size());
		return vertecis.get(ranIndex);
	}
	
	private static String getRandomConstantString (int length) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < length; i++) {
			char character = (char) (random.nextInt(94) + 32);
			sb.append (character);
		}
		return sb.toString();
	}
	
	private static int getIndex (int num, int [] list) {
		int runningTotal = 0;
		for (int i = 0; i < list.length; i++) {
			runningTotal = runningTotal + list[i];
			if (runningTotal > num) {
				return i;
			}
		}
		for (int i = list.length - 1; i >= 0; i--) {
			if (list[i] > 0) {
				return i;
			}
		}
		return -1;
	}
	
	private static void println (String msg) {
		System.out.println("[RandomTest] " + msg);
	}
	
	static class Result {
		long time;
		boolean result;
		
		public Result (long time, boolean result) {
			this.time = time;
			this.result = result;
		}
	}
}

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
import java.util.ArrayList;
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
import gov.nasa.jpf.symbc.string.StringComparator;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringPathCondition;
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

public class RandomTest2 {
	
	static int totalWeight;
	static SymbolicIntegerGenerator sig;
	static Random random;
	static int counter;
	static PathCondition pc;
	static StringPathCondition spc;
	
	static List<StringExpression> stringExpressions;
	static List<IntegerExpression> integerExpressions;
	
	private static final String Z3_Inc = "Z3 Inc";
	private static final String Z3 = "Z3";
	private static final String Automata = "Automata";
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
		Profile p = get3smallSetOfEdges();
		//Profile p = get3goodSetOfEdges();
		
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
		//args = new String[]{"-848008875103978746"};
		//args = new String[]{"3312688664425948851"};
		//4513434549285285031
		//args = new String[]{"3351366673402388866"};
		//args = new String[]{"2193013974386577201"};
		//args = new String[]{"-3822332894774604718"};
		//args = new String[]{"5565495604158725196"};
		//args = new String[]{"-4157825652249003335"};
		if (args.length == 0) {
			System.out.println("[data]," + p);
			for (int i = 0; i < 1000; i++) {
				random = new Random();
				long seed = random.nextLong();
				System.out.println("Starting: " + seed);
				generateRandomProblem (p, seed);
				Result z3dur = go (p, seed, Z3_Inc);
				generateRandomProblem (p, seed);
				Result autodur = go (p, seed, Automata);
				System.out.print("[data],\""+seed+"\","+z3dur.time+","+autodur.time);
				if (z3dur.result != autodur.result) {
					System.out.print(",warning");
				}
				System.out.println();
				
			}
		}
		else if (args.length == 1) {
			random = new Random();
			long seed = Long.parseLong(args[0]);
			generateRandomProblem(p, seed);
			System.out.println(spc.toString());
			System.out.println(pc.toString());
			if (showOnlyGraph == false) {
				System.out.println("[RandomTest] Calling with z3");
				Result z3dur = go (p, seed, Z3_Inc);
				System.out.println("[RandomTest] Calling with automata");
				generateRandomProblem (p, seed);
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
				generateRandomProblem(p, seed);
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
		System.exit(0);
		
	}
	
	public static Result go (Profile p, long seed, String Solver) {
		//System.out.println(sg.toDot());
		long time = System.currentTimeMillis();
		int result = -1;
		if (Solver.equals (Z3_Inc)) {
			System.out.println("[RandomTest] branch 1");
			SymbolicStringConstraintsGeneral.TIMEOUT = TEST_TIMEOUT;
			SymbolicStringConstraintsGeneral.timedOut = false;
			SymbolicStringConstraintsGeneral.timer = new Timer();
			SymbolicStringConstraintsGeneral.timer.schedule(new SymbolicStringTimeOut(), SymbolicStringConstraintsGeneral.TIMEOUT);
			try {
				System.out.println("[RandomTest] Z3 inc staring");
				
				result = callJPF("z3_inc");
								
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
				result = callJPF("automata");
				System.out.println("[RandomTest] Automata done");
			} catch (SymbolicStringTimedOutException e) {
				SymbolicStringConstraintsGeneral.timer.cancel();
				return new Result (-2, false);
			}
			SymbolicStringConstraintsGeneral.timer.cancel();
		}
		long dur = System.currentTimeMillis() - time;
		//System.out.println("[output] " + Solver + ": " + dur);
		if (result == 0) {
			return new Result(dur, false);
		} else if (result == 1) {
			return new Result(dur, true);
		} else if (result == 2) {
			return new Result(-2, false);
		} else {
			throw new RuntimeException("Unexpected result");
		}

	}
	
	public static int callJPF (String solver) {
		try {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=" + TEST_TIMEOUT};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			boolean result = spc.simplify();
			if (result == false) {
				return 0;
			} else {
				return 1;
			}
		} catch (SymbolicStringTimedOutException e) {
			return 2;
		}
	}
	
	public static StringGraph generateRandomProblem (Profile p, long seed) {
		StringGraph result = new StringGraph();
		pc = new PathCondition();
		spc = new StringPathCondition(pc);
		stringExpressions = new ArrayList<StringExpression>();
		integerExpressions = new ArrayList<IntegerExpression>();
		//System.out.println("Random seed: " + seed);
		random.setSeed(seed);
		counter = 0;
		
		totalWeight = 0;
		for (int i = 0; i < p.listOfEdgesToBeUsed.length; i++) {
			totalWeight = totalWeight + p.listOfEdgesToBeUsed[i];
		}
		
		vertexCounter = 0;
		
		sig = new SymbolicIntegerGenerator();
		char character = 'a';
		
		for (int i = 0; i < p.amountOfStringVar; i++) {
			stringExpressions.add(new StringSymbolic("stringvar" + i));
		}
		
		for (int i = 0; i < p.amountOfStringCons; i++) {
			String name = getRandomConstantString (random.nextInt(p.stringConsMaxLength) + 1);
			stringExpressions.add(new StringConstant(name));
		}
		
		for (int i = 0; i < p.amountOfIntegerCons; i++) {
			integerExpressions.add(new IntegerConstant(random.nextInt(200)));
		}
		
		for (int i = 0; i < p.amountOfIntegerVar; i++) {
			integerExpressions.add(new SymbolicInteger("SYM_INT_" + i));
		}
		
		for (int i = 0; i < p.amountOfEdges; i++ ) {
			double ran = random.nextDouble();
			ran = ran * totalWeight;
			ran = Math.round (ran);
			int index = getIndex ((int) ran, p.listOfEdgesToBeUsed);
			switch (index) {
			case 0:
				//EdgeCharAt
				handleEdgeCharAt();
				break;
			case 1:
				//EdgeConcat
				handleEdgeConcat();
				break;
			case 2:
				//EdgeContains
				handleEdgeContains ();
				break;
			case 3:
				//EdgeEndsWith
				handleEdgeEndsWith ();
				break;
			case 4:
				//EdgeEqual
				handleEdgeEqual ();
				break;
			case 5:
				//EdgeIndexOf
				handleEdgeIndexOf ();
				break;
			case 6:
				//EdgeIndexOf2
				handleEdgeIndexOf2 ();
				break;
			case 7:
				//EdgeIndexOfChar
				handleEdgeIndexOfChar ();
				break;
			case 8:
				//EdgeIndexOfChar2
				handleEdgeIndexOfChar2 ();
				break;
			case 9:
				//EdgeLastIndexOf
				handleEdgeLastIndexOf ();
				break;
			case 10:
				//EdgeLastIndexOf2
				handleEdgeLastIndexOf2 ();
				break;
			case 11:
				//EdgeLastIndexOfChar
				handleEdgeLastIndexOfChar ();
				break;
			case 12:
				//EdgeLastIndexOfChar2
				handleEdgeLastIndexOfChar2 ();
				break;
			case 13:
				//EdgeNotContains
				handleEdgeNotContains ();
				break;
			case 14:
				//EdgeNotEndsWith
				handleEdgeNotEndsWith ();
				break;
			case 15:
				//EdgeNotEquals
				handleEdgeNotEquals ();
				break;
			case 16:
				//EdgeNotStartsWith
				handleEdgeNotStartsWith ();
				break;
			case 17:
				//EdgeReplaceCharChar
				throw new RuntimeException ("Not implemented yet");
			case 18:
				//EdgeStartsWith
				handleEdgeStartsWith ();
				break;
			case 19:
				//EdgeSubstring1Equal
				handleEdgeSubstring1Equal();
				break;
			case 20:
				//EdgeSubstring2Equal
				handleEdgeSubstring2Equal();
				break;
			case 21:
				//EdgeTrimEqual
				handleEdgeTrimEqual();
				break;
			}
		}
		
		return result;
	}
	
	private static void handleEdgeTrimEqual () {
		StringExpression se1, se2;
		
		se1 = randomString();
		se2 = randomString();
		
		while (!unique(se1, se2)) {
			se1 = randomString();
			se2 = randomString();
		}
		
		spc._addDet(StringComparator.EQUALS, se1._trim(), se2);
	}
	
	private static void handleEdgeSubstring1Equal () {
		StringExpression se1;
		IntegerExpression ie1, ie2;
		
		se1 = randomString();
		ie1 = randomInteger();
		ie2 = randomInteger();
		
		while (!unique(ie1, ie2)) {
			ie1 = randomInteger();
			ie2 = randomInteger();
		}
		
		StringExpression newse = se1._subString(ie1);
		
		pc._addDet(randomComp(), newse, ie2);
		
		stringExpressions.add(newse);
	}
	
	private static void handleEdgeSubstring2Equal () {
		StringExpression se1;
		IntegerExpression ie1, ie2, ie3;
		
		se1 = randomString();
		ie1 = randomInteger();
		ie2 = randomInteger();
		ie3 = randomInteger();
				
		while (!unique(ie1, ie2, ie3)) {
			ie1 = randomInteger();
			ie2 = randomInteger();
			ie3 = randomInteger();
		}
		
		StringExpression newse = se1._subString(ie1, ie2);
		
		pc._addDet(randomComp(), newse, ie3);
		
		stringExpressions.add(newse);
	}
	
	private static void handleEdgeIndexOf () {
		StringExpression se1, se2;
		IntegerExpression ie1;
		
		se1 = randomString();
		ie1 = randomInteger();
		se2 = randomString();
		
		while (!unique(se1, se2)) {
			se1 = randomString();
			se2 = randomString();
		}
		
		IntegerExpression newse = se1._indexOf(se2);
		
		pc._addDet(randomComp(), newse, ie1);
		
		integerExpressions.add(newse);
	}
	
	private static void handleEdgeLastIndexOf () {
		StringExpression se1, se2;
		IntegerExpression ie1;
		
		se1 = randomString();
		ie1 = randomInteger();
		se2 = randomString();
		
		while (!unique(se1, se2)) {
			se1 = randomString();
			se2 = randomString();
		}
		
		IntegerExpression newie = se1._lastIndexOf(se2); 
		
		pc._addDet(randomComp(), newie, ie1);
		
		integerExpressions.add(newie);
	}
	
	private static void handleEdgeIndexOfChar () {
		StringExpression se1;
		IntegerExpression ie1, ie2;
		
		se1 = randomString();
		ie1 = randomInteger();
		ie2 = randomInteger();
		
		while (!unique(ie1, ie2)) {
			ie1 = randomInteger();
			ie2 = randomInteger();
		}
		
		IntegerExpression newie = se1._indexOf(ie2);
		
		pc._addDet(randomComp(), newie, ie1);
		
		integerExpressions.add(newie);
	}
	
	private static void handleEdgeLastIndexOfChar () {
		StringExpression se1;
		IntegerExpression ie1, ie2;
		
		se1 = randomString();
		ie1 = randomInteger();
		ie2 = randomInteger();
		
		while (!unique(ie1, ie2)) {
			ie1 = randomInteger();
			ie2 = randomInteger();
		}
		
		IntegerExpression newie = se1._lastIndexOf(ie2);
		
		pc._addDet(randomComp(), newie, ie1);
		
		integerExpressions.add(newie);
	}
	
	private static void handleEdgeIndexOfChar2 () {
		StringExpression se1, se2;
		IntegerExpression ie1, ie2;
		
		se1 = randomString();
		se2 = randomString();
		ie1 = randomInteger();
		ie2 = randomInteger();
		
		while (!unique(se1, se2)) {
			se1 = randomString();
			se2 = randomString();
		}
		
		while (!unique(ie1, ie2)) {
			ie1 = randomInteger();
			ie2 = randomInteger();
		}
		
		IntegerExpression newie = se1._indexOf(se2, ie1);
		
		pc._addDet(randomComp(), newie, ie2);
		
		integerExpressions.add(newie);
	}
	
	private static void handleEdgeLastIndexOfChar2 () {
		StringExpression se1, se2;
		IntegerExpression ie1, ie2;
		
		se1 = randomString();
		se2 = randomString();
		ie1 = randomInteger();
		ie2 = randomInteger();
		
		while (!unique(se1, se2)) {
			se1 = randomString();
			se2 = randomString();
		}
		
		while (!unique(ie1, ie2)) {
			ie1 = randomInteger();
			ie2 = randomInteger();
		}
		
		IntegerExpression newie = se1._lastIndexOf(se2, ie1);
		
		pc._addDet(randomComp(), newie, ie2);
		
		integerExpressions.add(newie);
	}
	
	private static void handleEdgeIndexOf2 () {
		StringExpression se1;
		IntegerExpression ie1, ie2, ie3;
		
		se1 = randomString();
		ie1 = randomInteger();
		ie2 = randomInteger();
		ie3 = randomInteger();
		
		while (!unique(ie1, ie2, ie3)) {
			ie1 = randomInteger();
			ie2 = randomInteger();
			ie3 = randomInteger();
		}
		
		IntegerExpression newie = se1._indexOf(ie3, ie1);
		
		pc._addDet(randomComp(), newie, ie2);
		
		integerExpressions.add(newie);
		
	}
	
	private static void handleEdgeLastIndexOf2 () {
		StringExpression se1, se2;
		IntegerExpression ie1, ie2;
		
		se1 = randomString();
		se2 = randomString();
		ie1 = randomInteger();
		ie2 = randomInteger();
		
		while (!unique(se1, se2)) {
			se1 = randomString();
			se2 = randomString();
		}
		
		while (!unique(ie1, ie2)) {
			ie1 = randomInteger();
			ie2 = randomInteger();
		}
		
		IntegerExpression newie = se1._lastIndexOf(se2, ie1); 
		
		pc._addDet(randomComp(), newie, ie2);
		
		integerExpressions.add(newie);
	}
	
	private static void handleEdgeCharAt () {
		vertexCounter++;
		IntegerExpression i1, i2;
		i1 = randomInteger();
		i2 = randomInteger();
		
		while (!unique(i1, i2)) {
			i1 = randomInteger();
			i2 = randomInteger();
		}
		
		StringExpression se1 = randomString();
		
		IntegerExpression newie = se1._charAt(i1);
		
		pc._addDet(randomComp(), newie, i2);
		
		integerExpressions.add(newie);
	}
	
	private static void handleEdgeConcat () {
		StringExpression se1 = randomString();
		StringExpression se2 = randomString();
		StringExpression se3 = randomString();
		
		while (!unique(se1, se2, se3)) {
			se1 = randomString();
			se2 = randomString();
			se3 = randomString();
		}
		
		StringExpression newse = se1._concat(se2);
		
		spc._addDet(StringComparator.EQUALS, newse, se3);
		
		stringExpressions.add(newse);
	}
	
	private static IntegerExpression randomInteger () {
		return integerExpressions.get(random.nextInt(integerExpressions.size()));
	}
	
	private static void handleEdgeStartsWith () {
		handleBooleanConstraint(StringComparator.STARTSWITH);
	}
		
	private static void handleEdgeNotEquals () {
		handleBooleanConstraint(StringComparator.NOTEQUALS);
	}
	
	private static void handleEdgeNotStartsWith () {
		handleBooleanConstraint(StringComparator.NOTSTARTSWITH);
	}
	
	private static void handleEdgeNotEndsWith () {
		handleBooleanConstraint(StringComparator.NOTENDSWITH);
	}
	
	private static void handleEdgeNotContains () {
		handleBooleanConstraint(StringComparator.NOTCONTAINS);
	}
	
	private static void handleEdgeEqual () {
		handleBooleanConstraint(StringComparator.EQUALS);
	}
	
	private static void handleEdgeEndsWith () {
		handleBooleanConstraint(StringComparator.ENDSWITH);
	}
	
	private static void handleEdgeContains () {
		handleBooleanConstraint(StringComparator.CONTAINS);
	}
	
	private static void handleBooleanConstraint (StringComparator sc) {
		StringExpression se1, se2;
		se1 = null;
		se2 = null;
		while (!unique(se1, se2)) {
			se1 = randomString();
			se2 = randomString();
		}
		spc._addDet(sc, se1, se2);
	}
	
	private static boolean unique (StringExpression se1, StringExpression se2) {
		if (se1 == null || se2 == null) return false;
		if (se1 == se2) return false;
		if (se1 instanceof StringConstant && se2 instanceof StringConstant) return false;
		return true;
	}
	
	
	private static boolean unique (StringExpression se1, StringExpression se2, StringExpression se3) {
		if (se1 == null || se2 == null || se3 == null) return false;
		if (se1 == se2 || se1 == se3 || se2 == se3) return false;
		if (se1 instanceof StringConstant && se2 instanceof StringConstant && se3 instanceof StringConstant) return false;
		return true;
	}
	
	private static boolean unique (IntegerExpression ie1, IntegerExpression ie2) {
		if (ie1 == null || ie2 == null) return false;
		if (ie1 == ie2) return false;
		return true;
	}
	
	private static boolean unique (IntegerExpression ie1, IntegerExpression ie2, IntegerExpression ie3) {
		if (ie1 == null || ie2 == null || ie3 == null) return false;
		if (ie1 == ie2 && ie1 == ie3 && ie2 == ie3) return false;
		return true;
	}
	
	private static StringExpression randomString() {
		return stringExpressions.get(random.nextInt(stringExpressions.size()));
	}
	
	private static Comparator randomComp () {
		boolean equals = random.nextBoolean();
		if (equals) {
			return Comparator.EQ;
		} else {
			return Comparator.NE;
		}
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

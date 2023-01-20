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

package gov.nasa.jpf.symbc.strings;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.util.test.TestJPF;
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
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;

import org.junit.Test;


public class TestABC extends TestJPF {
	
	String[] solvers = new String[]{"ABC"};
	private static void callerName(){
		System.out.println(new Exception().getStackTrace()[1]);
	}
	
	@Test
	//NOTEQUALS
	public void Test01_1 () {
		System.out.println("Test01_1");
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3);		
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().equals(var2.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
		}
	}
	
	@Test
	public void Test01_2 () {
		System.out.println("Test01_2");
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var3);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().equals(var2.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(!var1.solution().equals(var3.solution()));
		}
	}
	
	
	@Test
	public void Test01_3 () {
		System.out.println("Test01_3");
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var[] = new StringSymbolic[10];
			for (int i = 0; i < var.length; i++) {
				var[i] = new StringSymbolic("var" + i);
			}
			for (int i = 0; i < var.length-1; i++) {
				for (int j = i+1; j < var.length; j++) {
					stringCurrentPC._addDet(StringComparator.NOTEQUALS, var[i], var[j]);
				}
			}
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			for (int i = 0; i < var.length-1; i++) {
				for (int j = i+1; j < var.length; j++) {
					assertTrue(!var[i].solution().equals(var[j].solution()));
				}
			}
			
		}
	}
	
	//NOTSTARTSWITH
	@Test
	public void Test02_1 () {
		System.out.println("Test02_1");
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			pc._addDet(Comparator.GE, var1._length(), new IntegerConstant(2));
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var2, var1);		
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().startsWith(var2.solution()));
		}
	}
	
	//No negatives
	@Test
	public void Test03_1 () {
		System.out.println("Test03_1");
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			pc._addDet(Comparator.GE, var1._length(), new IntegerConstant(2));
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var1);		
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().equals(var2.solution()));
		}
	}
	
	//NOTENDSWITH
	@Test
	public void Test4_1 () {
		System.out.println("Test04_1");
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			pc._addDet(Comparator.GE, var1._length(), new IntegerConstant(2));
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, var2, var1);		
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().endsWith(var2.solution()));
		}
	}
	
	//NOTCONTAINS
	@Test
	public void Test5_1 () {
		System.out.println("Test05_1");
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			pc._addDet(Comparator.GE, var1._length(), new IntegerConstant(2));
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var2, var1);		
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().contains(var2.solution()));
		}
	}
	
	//STARTSWITH
	@Test
	public void Test6_1 () {
		System.out.println("Test06_1");
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().startsWith("a"));
			assertTrue(var2.solution().startsWith("b"));
		}
	}
	
	@Test
	public void Test6_2 () {
		System.out.println("Test06_2");
		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().startsWith("a"));
			assertTrue(!var2.solution().startsWith("b"));
		}
	}

	@Test
	public void Test6_3 () {
		System.out.println("Test06_3");
		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().startsWith("a"));
			assertTrue(var2.solution().startsWith("b"));
		}
	}
	
	@Test
	public void Test6_4 () {
		System.out.println("Test06_4");
		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().startsWith("a"));
			assertTrue(!var2.solution().startsWith("b"));
		}
	}
	
	@Test
	public void Test7_1 () {
		System.out.println("Test07_1");
		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().startsWith("a"));
			assertTrue(var2.solution().startsWith("b"));
		}
	}
	
	@Test
	public void Test7_2 () {

		System.out.println("Test07_2");
		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().startsWith("a"));
			assertTrue(!var2.solution().startsWith("b"));
		}
	}

	@Test
	public void Test7_3 () {

		System.out.println("Test07_3");
		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().startsWith("a"));
			assertTrue(var2.solution().startsWith("b"));
		}
	}
	
	@Test
	public void Test7_4 () {

		System.out.println("Test067_4");
		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().startsWith("a"));
			assertTrue(!var2.solution().startsWith("b"));
		}
	}
	
	@Test
	public void Test8_1 () {
		System.out.println("Test08_1");
		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().equals("a"));
			assertTrue(var2.solution().equals("b"));
		}
	}
	
	@Test
	public void Test8_2 () {

		System.out.println("Test08_2");
		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			System.out.println(SymbolicStringConstraintsGeneral.getSolution());
			assertTrue(result);
			assertTrue(var1.solution().equals("a"));
			assertTrue(var2.solution() == null || !var2.solution().equals("b"));
		}
	}

	@Test
	public void Test8_3 () {
		System.out.println("Test08_3");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().equals("a"));
			assertTrue(var2.solution().equals("b"));
		}
	}
	
	@Test
	public void Test8_4 () {
		System.out.println("Test08_4");

		
		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().equals("a"));
			assertTrue(!var2.solution().equals("b"));
		}
	}
	
	@Test
	public void Test9_1 () {
		System.out.println("Test09_1");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().contains("a"));
			assertTrue(var2.solution().contains("b"));
		}
	}
	
	@Test
	public void Test9_2 () {
		System.out.println("Test09_2");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			System.out.println(SymbolicStringConstraintsGeneral.getSolution());
			assertTrue(result);
			assertTrue(var1.solution().contains("a"));
			assertTrue(!var2.solution().contains("b"));
		}
	}

	@Test
	public void Test9_3 () {
		System.out.println("Test09_3");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().contains("a"));
			assertTrue(var2.solution().contains("b"));
		}
	}
	
	@Test
	public void Test9_4 () {
		System.out.println("Test09_4");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("b"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().contains("a"));
			assertTrue(!var2.solution().contains("b"));
		}
	}
	
	//TRIM
	@Test
	public void Test10_1 () {
		System.out.println("Test10_1");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringExpression var2 = var1._trim();
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("cc"), var2);
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("cc"));
			assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test10_2 () {
		System.out.println("Test10_2");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringExpression var2 = var1._trim();
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("cc"), var2);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var2.solution().equals("cc"));
			assertTrue(!var1.solution().trim().equals("cc"));
		}
	}
	
	
	//CONCAT
	@Test
	public void Test11_1 () {
		System.out.println("Test11_1");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("b"), var2);
			StringExpression var3 = var1._concat(var2);
			pc._addDet(Comparator.LE, var3._length(), 10);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().contains("a"));
			assertTrue(var2.solution().contains("b"));
			assertTrue(var1.solution().concat(var2.solution()).equals(var3.solution()));
			assertTrue(var3.solution().length() < 10);
		}
	}
	
	@Test
	public void Test11_2 () {
		System.out.println("Test11_2");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("b"), var2);
			StringExpression var3 = var1._concat(var2);
			pc._addDet(Comparator.LE, var3._length(), 10);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().contains("a"));
			assertTrue(var2.solution().contains("b"));
			assertTrue(var1.solution().concat(var2.solution()).equals(var3.solution()));
			assertTrue(var3.solution().length() < 10);
		}
	}
	
	@Test
	public void Test11_3 () {
		System.out.println("Test11_3");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("b"), var2);
			StringExpression var3 = var1._concat(var2);
			pc._addDet(Comparator.LE, var3._length(), 10);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().contains("a"));
			assertTrue(!var2.solution().contains("b"));
			assertTrue(var1.solution().concat(var2.solution()).equals(var3.solution()));
			assertTrue(var3.solution().length() < 10);
		}
	}
	
	@Test
	public void Test11_4 () {
		System.out.println("Test11_4");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("b"), var2);
			StringExpression var3 = var1._concat(var2);
			pc._addDet(Comparator.LE, var3._length(), 10);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().contains("a"));
			assertTrue(!var2.solution().contains("b"));
			assertTrue(var1.solution().concat(var2.solution()).equals(var3.solution()));
			assertTrue(var3.solution().length() < 10);
		}
	}

	@Test
	public void Test11_5 () {
		System.out.println("Test11_5");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("b"), var2);
			StringExpression var3 = var1._concat(var2);
			pc._addDet(Comparator.GT, var3._length(), 10);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().contains("a"));
			assertTrue(var2.solution().contains("b"));
			assertTrue(var1.solution().concat(var2.solution()).equals(var3.solution()));
			assertTrue(var3.solution().length() > 10);
		}
	}
	
	@Test
	public void Test11_6 () {
		System.out.println("Test11_6");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("b"), var2);
			StringExpression var3 = var1._concat(var2);
			pc._addDet(Comparator.GT, var3._length(), 10);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().contains("a"));
			assertTrue(var2.solution().contains("b"));
			assertTrue(var1.solution().concat(var2.solution()).equals(var3.solution()));
			assertTrue(var3.solution().length() > 10);
		}
	}
	
	@Test
	public void Test11_7 () {
		System.out.println("Test11_7");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("b"), var2);
			StringExpression var3 = var1._concat(var2);
			pc._addDet(Comparator.GT, var3._length(), 10);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var1.solution().contains("a"));
			assertTrue(!var2.solution().contains("b"));
			assertTrue(var1.solution().concat(var2.solution()).equals(var3.solution()));
			assertTrue(var3.solution().length() > 10);
		}
	}
	
	@Test
	public void Test11_8 () {
		System.out.println("Test11_8");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("b"), var2);
			StringExpression var3 = var1._concat(var2);
			pc._addDet(Comparator.GT, var3._length(), 10);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().contains("a"));
			assertTrue(!var2.solution().contains("b"));
			assertTrue(var1.solution().concat(var2.solution()).equals(var3.solution()));
			assertTrue(var3.solution().length() > 10);
		}
	}
	
	//INDEXOF
	@Test
	public void Test12_1 () {
		System.out.println("Test12_1");

		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1);
			pc._addDet(Comparator.LE, var1._length(), 10);
			pc._addDet(Comparator.GT, var1._indexOf(new StringConstant("a")), 0);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue("Solver " + solver + " failed",  !result);
			/*assertTrue(var1.solution().startsWith("aa"));
			assertTrue(var1.solution().indexOf("a") > 0);*/
			
		}
	}
	
	@Test
	public void Test12_2 () {
		System.out.println("Test12_2");

		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bb"), var1);
			pc._addDet(Comparator.GT, var1._indexOf(new StringConstant("a")), 0);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().startsWith("bb"));
			assertTrue(var1.solution().indexOf("a") > 0);
			
		}
	}
	
	@Test
	public void Test12_3 () {
		System.out.println("Test12_3");

		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bb"), var1);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("a")), -1);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().startsWith("bb"));
			assertTrue(var1.solution().indexOf("a") == -1);
			
		}
	}
	
	@Test
	public void Test12_4 () {
		System.out.println("Test12_4");

		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bb"), var1);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("b")), -1);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test12_5 () {
		System.out.println("Test12_5");

		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bb"), var1);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("b")), 1);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(!result);
		}
	}
	
	@Test
	//TODO: Could do with a speedup
	public void Test13_1 () {
		System.out.println("Test13_1");

		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1);
			SymbolicInteger si = new SymbolicInteger("int1");
			pc._addDet(Comparator.LE, var1._length(), 10);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("a"), new IntegerConstant(5)), si);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue("Solver " + solver + " failed",  result);
			assertTrue(var1.solution().startsWith("aa"));
			System.out.printf("var1.solution() '%s'\n", var1.solution());
			System.out.printf("si.solution() '%s'\n", si.solution());
			assertTrue(var1.solution().indexOf("a", 5) == si.solution());
			
		}
	}
	
	@Test
	public void Test13_2 () {
		System.out.println("Test13_2");

		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bb"), var1);
			SymbolicInteger si = new SymbolicInteger("int1");
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("a"), new IntegerConstant(5)), si);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().startsWith("bb"));
			assertTrue(var1.solution().indexOf("a", 5) == si.solution());
			
		}
	}
	
	@Test
	public void Test13_3 () {
		System.out.println("Test13_3");

		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1);
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("bb"), var2);
			pc._addDet(Comparator.GT, var1._indexOf(var2), 0);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().startsWith("aa"));
			assertTrue(var2.solution().endsWith("bb"));
			assertTrue(var1.solution().indexOf(var2.solution()) > 0);
			
		}
	}
	
	@Test
	public void Test14_1 () {
		System.out.println("Test14_1");

		/*
		 	"SYM_a"->"C_CONST_gLR" [label="StartsWith"]
			"C_CONST_kR"->"SYM_a" [label="!StartsWith"]
			"C_CONST_O4+]"->"SYM_a" [label="!StartsWith"]
		 */
		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("gLR"), var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var1, new StringConstant("kR"));
			//stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var1, new StringConstant("O4+]"));
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().startsWith("gLR"));
			assertTrue(!var1.solution().startsWith("kR"));
			
		}
	}
	
	@Test
	public void Test14_2 () {
		System.out.println("Test14_2");

		/*
		 	"SYM_b"->"C_CONST_Y&v^" [label="EndsWith"]
			"SYM_a"->"SYM_b" [label="!Equal", dir=both]
			"C_CONST_N@"->"SYM_b" [label="!EndsWith"]
		 */
		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("Y&v^"), var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, var1, new StringConstant("N@"));
			//stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var1, new StringConstant("O4+]"));
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().endsWith("Y&v^"));
			assertTrue(!var1.solution().startsWith("N@"));
			
		}
	}
	
	@Test
	public void Test14_3 () {
		System.out.println("Test14_3");

		/*
		 	"SYM_b"->"C_CONST_9u" [label="StartsWith"]
			"SYM_a"->"C_CONST_9u" [label="EndsWith"]
			"SYM_a"->"SYM_b" [label="EdgeNotContains"]
		 */
		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("9u"), var1);
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("9u"), var2);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var2, var1);
			//stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var1, new StringConstant("O4+]"));
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().startsWith("9u"));
			assertTrue(var2.solution().endsWith("9u"));
			assertTrue(!var1.solution().contains(var2.solution()));
		}
	}
	
	@Test
	public void Test14_4 () {
		System.out.println("Test14_4");

		//(stringvar1 notequals stringvar0) && (stringvar0 endswith stringvar1) && (stringvar1 endswith CONST_M.m)
		
		String[] solvers = new String[]{"ABC"};
		//String[] solvers = new String[]{"ABC", "z3_inc"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var0 = new StringSymbolic("var0");
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("M.m"), var1);
			stringCurrentPC._addDet(StringComparator.ENDSWITH, var1, var0);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var0, var1);
			//stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var1, new StringConstant("O4+]"));
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			System.out.println(var0.solution());
			System.out.println(var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().startsWith("M.m"));
			assertTrue(var0.solution().endsWith(var1.solution()));
			assertTrue(!var1.solution().equals(var0.solution()));
		}
		
	}
	
	@Test
	public void Test15_1 () {
		System.out.println("Test15_1");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringSymbolic var1 = new StringSymbolic("var1");
			StringExpression var2 = StringSymbolic._valueOf(var1);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("cc"), var2);
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("cc"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test15_2 () {
		System.out.println("Test15_2");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			IntegerConstant var1 = new IntegerConstant(5);
			StringExpression var2 = StringSymbolic._valueOf(var1);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("5"), var2);
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("cc"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test15_3 () {
		System.out.println("Test15_3");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			SymbolicInteger var1 = new SymbolicInteger("var1");
			StringExpression var2 = StringSymbolic._valueOf(var1);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("5"), var2);
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test16_1 () {
		System.out.println("Test16_1");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("hello, world");
			StringExpression var2 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var1._replace("hello", "world"));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test16_2 () {
		System.out.println("Test16_2");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("hello, world");
			StringExpression var2 = new StringSymbolic("var2");
			StringExpression var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var1._replace(var3, "world"));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test16_3 () {
		System.out.println("Test16_3");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("hello, world");
			StringExpression var2 = new StringSymbolic("var2");
			StringExpression var3 = new StringSymbolic("var3");
			StringExpression var4 = new StringSymbolic("var4");
			
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var1._replace(var3, var4));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test16_4 () {
		System.out.println("Test16_4");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("hello, world");
			StringExpression var2 = new StringSymbolic("var2");
			StringExpression var3 = new StringSymbolic("var3");
			StringExpression var4 = new StringSymbolic("var4");
			
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3._replace(var1, var4));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test17_1 () {
		System.out.println("Test17_1");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var0 = new StringSymbolic("var0");
			StringExpression var1 = new StringConstant("hello, ");
			StringExpression var2 = var0._concat("world");
			StringExpression var3 = new StringSymbolic("var3");			
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var2._replace(var1, "So long, "));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test18_1 () {
		System.out.println("Test18_1");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var0 = new StringSymbolic("var0");
			StringExpression var1 = new StringConstant("hello, ");
			StringExpression var2 = var0._concat("world");
			StringExpression var3 = new StringSymbolic("var3");			
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var2._replaceFirst(var1, "So long, "));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	
	@Test
	public void Test19_1 () {
		System.out.println("Test19_1");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("hello, world. hello mars");
			StringExpression var2 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var1._replaceFirst("hello", "goodbye, cruel"));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test19_2 () {
		System.out.println("Test19_2");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("hello, world. hello, mars");
			StringExpression var2 = new StringSymbolic("var2");
			StringExpression var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var1._replaceFirst(var3, "Goodbye, cruel "));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test19_3 () {
		System.out.println("Test19_3");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("hello, world. hello, mars");
			StringExpression var2 = new StringSymbolic("var2");
			StringExpression var3 = new StringSymbolic("var3");
			StringExpression var4 = new StringSymbolic("var4");
			
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var1._replaceFirst(var3, var4));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test19_4 () {
		System.out.println("Test19_4");

		String[] solvers = new String[]{"ABC"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("hello, world. hello, mars.");
			StringExpression var2 = new StringSymbolic("var2");
			StringExpression var3 = new StringSymbolic("var3");
			StringExpression var4 = new StringSymbolic("var4");
			
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3._replaceFirst(var1, var4));
			System.out.println("D4");
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("5"));
			//assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test_1_00_1 () {
		callerName();
		
		getClass().getMethods();
		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	
	
	@Test
	public void Test_1_1_1 () {
		callerName();
		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_1_2 () {
		callerName();
		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("b"), var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_1_3 () {
		callerName();
		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var2, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_1_4 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var3, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_2_1 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_2_2 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("b"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_2_3 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, var2, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_2_4 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, var3, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_3_1 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_3_2 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("b"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_3_3 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.CONTAINS, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var2, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_3_4 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.CONTAINS, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var3, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_4_1 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringExpression se1 = new StringConstant("a")._concat(var1);
			stringCurrentPC._addDet(StringComparator.EQUALS, se1, new StringConstant("ab"));
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_4_2 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringExpression se1 = new StringConstant("a")._concat(var1);
			stringCurrentPC._addDet(StringComparator.EQUALS, se1, new StringConstant("cd"));
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_4_3 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringExpression se1 = var1._concat(new StringConstant("b"));
			stringCurrentPC._addDet(StringComparator.EQUALS, se1, new StringConstant("ab"));
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_4_4 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringExpression se1 = var1._concat(new StringConstant("b"));
			stringCurrentPC._addDet(StringComparator.EQUALS, se1, new StringConstant("dc"));
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_5_1 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_5_2 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("b"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_5_3 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var2, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_5_4 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var3, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_5_5 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_5_6 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("b"), var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_5_7 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.CONTAINS, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var2, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_5_8 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.CONTAINS, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var3, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_6_1 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_6_2 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("b"), var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_6_3 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var2, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_6_4 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.ENDSWITH, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var3, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_6_5 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_6_6 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("b"), var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("a"), var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_6_7 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.CONTAINS, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, var2, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test_1_6_8 () {
		callerName();

		//String[] solvers = new String[]{"z3", "automata", "z3_inc"};
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0",
					"+symbolic.string_preprocess_only=true"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.CONTAINS, var2, var1);
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, var3, var1);
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
		}
	}
	
	@Test
	public void Test_1_7_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("a"), new StringConstant("b"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_7_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("a"), new StringConstant("a"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_8_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("b"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_8_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_9_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("b"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_9_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_10_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("b"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_10_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("c"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_11_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("b"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_11_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("c"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_12_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("d"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_12_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("c"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_13_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("d"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_13_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("c"), new StringConstant("abc"));
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_14_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('a'));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('a'));
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_14_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('a'));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('b'));
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_15_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('a'));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_15_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('b'));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_15_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._charAt(new SymbolicInteger("sym1")), new IntegerConstant('a'));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc);
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_15_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		SymbolicInteger si =  new SymbolicInteger("sym1");
		pc._addDet(Comparator.EQ, var1._charAt(si), new IntegerConstant('d'));
		pc._addDet(Comparator.LT, si, new IntegerConstant(3));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_16_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('a'));
		stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("abc"), var1);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_16_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('b'));
		stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("abc"), var1);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_16_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._charAt(new SymbolicInteger("sym1")), new IntegerConstant('a'));
		stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc);
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_16_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		SymbolicInteger si =  new SymbolicInteger("sym1");
		stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("abc"), var1);
		pc._addDet(Comparator.EQ, var1._charAt(var1._length()._minus(1)), new IntegerConstant('d'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_17_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		SymbolicInteger si =  new SymbolicInteger("sym1");
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("abc"), var1);
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc);
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_17_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		SymbolicInteger si =  new SymbolicInteger("sym1");
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_17_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		SymbolicInteger si =  new SymbolicInteger("sym1");
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("b"), var1);
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant('a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc);
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_18_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		StringSymbolic var2 = new StringSymbolic("var2");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var2._indexOf(new StringConstant("def")), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_18_3 () {
		callerName();

		//TODO: Improve
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc);
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_18_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("def")), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_18_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("def")), new IntegerConstant(5));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_18_6 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		StringSymbolic var2 = new StringSymbolic("var2");
		pc._addDet(Comparator.EQ, var1._indexOf(var2), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var2);
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("def")), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_19_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new SymbolicInteger("int1"));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_19_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_19_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc")), new SymbolicInteger("int1"));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_19_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc")), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_19_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bcd")), new IntegerConstant(1));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_19_6 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bcd")), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_20_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_20_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("b")), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_20_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("d")), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_21_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_21_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("ab")), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_21_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc")), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_22_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(-1));
		stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_22_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc")), new IntegerConstant(-1));
		stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_23_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(3)), new IntegerConstant((int) 'b'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_23_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(2)), new IntegerConstant((int) 'e'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_23_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(4)), new IntegerConstant((int) 'e'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_23_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		IntegerExpression ie1 = new SymbolicInteger("ie1");
		IntegerExpression ie2 = new SymbolicInteger("ie2");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), ie1);
		pc._addDet(Comparator.EQ, var1._charAt(ie2), new IntegerConstant((int) 'e'));
		pc._addDet(Comparator.EQ, ie1, new IntegerConstant(2));
		pc._addDet(Comparator.GE, ie2, new IntegerConstant(2));
		pc._addDet(Comparator.LE, ie2, new IntegerConstant(4));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_23_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		IntegerExpression ie1 = new SymbolicInteger("ie1");
		IntegerExpression ie2 = new SymbolicInteger("ie2");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), ie1);
		pc._addDet(Comparator.EQ, var1._charAt(ie2), new IntegerConstant((int) 'e'));
		pc._addDet(Comparator.EQ, ie1, new IntegerConstant(2));
		pc._addDet(Comparator.GE, ie2, new IntegerConstant(2));
		pc._addDet(Comparator.LE, ie2, new IntegerConstant(5));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_24_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_24_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_25_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new SymbolicInteger("ie1"));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_25_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new SymbolicInteger("ie1"));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("b"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_25_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(-1));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_25_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(1));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	
	@Test
	public void Test_1_26_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_26_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(1));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_26_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_26_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(1));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_27_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_27_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_27_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(1));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_28_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new SymbolicInteger("ie1"));
		stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_28_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(-1));
		stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_28_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(-1));
		stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_29_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(1));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_29_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(1));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_29_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(1));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(0)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_29_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(1));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(0)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_29_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(0));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_30_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(0));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(0));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_30_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(1));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(1));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_30_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(1));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_30_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'c')), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(1));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_31_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(2)), new SymbolicInteger("ie1"));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("def"), new IntegerConstant(5)), new SymbolicInteger("ie2"));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_31_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(2)), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("def"), new IntegerConstant(2)), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_32_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(2)), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_32_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("b"), new IntegerConstant(2)), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_32_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("d"), new IntegerConstant(2)), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_33_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(0)), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_33_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("ab"), new IntegerConstant(0)), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_33_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc"), new IntegerConstant(0)), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_33_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(2)), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_33_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("ab"), new IntegerConstant(2)), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_33_6 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc"), new IntegerConstant(2)), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_34_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(0)), new SymbolicInteger("int1"));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_34_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(0)), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_34_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc"), new IntegerConstant(0)), new SymbolicInteger("int1"));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_34_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc"), new IntegerConstant(0)), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_34_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bcd"), new IntegerConstant(0)), new IntegerConstant(1));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_34_6 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bcd"), new IntegerConstant(0)), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_34_7 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(3)), new SymbolicInteger("int1"));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_34_8 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(3)), new IntegerConstant(3));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_34_9 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc"), new IntegerConstant(3)), new SymbolicInteger("int1"));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_34_10 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc"), new IntegerConstant(3)), new IntegerConstant(3));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc);
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_34_11 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bcd"), new IntegerConstant(3)), new IntegerConstant(3));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_34_12 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bcd"), new IntegerConstant(3)), new IntegerConstant(3));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	/*@Test
	public void Test_1_34_13 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("ab"), new IntegerConstant(2)), new IntegerConstant(2));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abcde"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc);
		assertTrue(!scg.isSatisfiable(pc));
	}*/
	
	@Test
	public void Test_1_35_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(0)), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(3)), new IntegerConstant((int) 'b'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_35_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(0)), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(2)), new IntegerConstant((int) 'e'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_35_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		IntegerExpression ie1 = new SymbolicInteger("ie1");
		IntegerExpression ie2 = new SymbolicInteger("ie2");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(0)), ie1);
		pc._addDet(Comparator.EQ, var1._charAt(ie2), new IntegerConstant((int) 'e'));
		pc._addDet(Comparator.EQ, ie1, new IntegerConstant(2));
		pc._addDet(Comparator.GE, ie2, new IntegerConstant(2));
		pc._addDet(Comparator.LE, ie2, new IntegerConstant(5));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_36_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'a'), new IntegerConstant(1)), new IntegerConstant(3));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'a'), new IntegerConstant(2)),  new IntegerConstant(4));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_36_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'a'), new IntegerConstant(1)), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'b'), new IntegerConstant(2)),  new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_36_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'a'), new IntegerConstant(1)), new IntegerConstant(3));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'b'), new IntegerConstant(2)),  new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_37_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'a'), new IntegerConstant(1)), new IntegerConstant(3));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_37_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'a'), new IntegerConstant(-1)), new IntegerConstant(-1));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_37_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'a'), new IntegerConstant(-1)), new IntegerConstant(1));
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_38_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'a'), new IntegerConstant(-1)), new IntegerConstant(1));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_38_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'a'), new IntegerConstant(0)), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
		
	}
	
	@Test
	public void Test_1_38_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'b'), new IntegerConstant(0)), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		
		assertTrue(scg.isSatisfiable(pc));
		
	}
	
	@Test
	public void Test_1_39_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'b'), new IntegerConstant(0)), new IntegerConstant(0));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
		
	}
	
	@Test
	public void Test_1_39_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((char)'b'), new IntegerConstant(1)), new SymbolicInteger("ie1"));
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		
		assertTrue(scg.isSatisfiable(pc));
		
	}
	
	@Test
	public void Test_1_40_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a'), new IntegerConstant(1)), new IntegerConstant(1));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_40_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b'), new IntegerConstant(1)), new IntegerConstant(1));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_40_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b'), new IntegerConstant(1)), new IntegerConstant(1));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(0)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_40_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a'), new IntegerConstant(0)), new IntegerConstant(0));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		System.out.println(pc); 
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_41_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a'), new IntegerConstant(2)), new IntegerConstant(0));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_42_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a'), new IntegerConstant(2)), new IntegerConstant(3));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(0));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_42_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a'), new IntegerConstant(2)), new IntegerConstant(3));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
		
	}
	
	@Test
	public void Test_1_42_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b'), new IntegerConstant(2)), new IntegerConstant(3));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
		
	}
	
	@Test
	public void Test_1_42_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b'), new IntegerConstant(4)), new IntegerConstant(5));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));	
	}
	
	@Test
	public void Test_1_43_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(2)), new IntegerConstant(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(0));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
		
	}
	
	@Test
	public void Test_1_43_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(2)), new IntegerConstant(3));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
		
	}
	
	@Test
	public void Test_1_43_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(2)), new IntegerConstant(3));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(4));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
		
	}
	
	@Test
	public void Test_1_43_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("def"), new IntegerConstant(2)), new IntegerConstant(4));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(4));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_44_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(5)), new IntegerConstant(6));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(4));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_44_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(5)), new IntegerConstant(6));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(6));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_44_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(5)), new IntegerConstant(6));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b')), new IntegerConstant(6));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_45_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(5)), new IntegerConstant(6));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b'), new IntegerConstant(2)), new IntegerConstant(6));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_45_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc"), new IntegerConstant(5)), new IntegerConstant(6));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a'), new IntegerConstant(2)), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_46_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a'), new IntegerConstant(5)), new IntegerConstant(6));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a'), new IntegerConstant(2)), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_46_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(5)), new IntegerConstant('a'));
		pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(5)), new IntegerConstant('b'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_47_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(6));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'b'), new IntegerConstant(2)), new IntegerConstant(6));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_47_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a')), new IntegerConstant(1));
		pc._addDet(Comparator.EQ, var1._indexOf(new IntegerConstant((int) 'a'), new IntegerConstant(2)), new IntegerConstant(6));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
		SymbolicConstraintsGeneral scg = new SymbolicConstraintsGeneral();
		assertTrue(scg.isSatisfiable(pc));
	}
	
	@Test
	public void Test_1_48_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_48_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(0));
		pc._addDet(Comparator.LT, var1._length(), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_48_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(0));
		pc._addDet(Comparator.LT, var1._length(), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_48_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		pc._addDet(Comparator.LT, var1._length(), new IntegerConstant(4));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_49_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_49_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("ab")), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_49_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc")), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_49_4 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc")), new IntegerConstant(6));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_49_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("def")), new IntegerConstant(6));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_50_1() {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(2)), new IntegerConstant('a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_50_2() {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(3)), new IntegerConstant('a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_50_3() {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(2)), new IntegerConstant('b'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_51_1() {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("a"), var1._subString(3,2));
		pc._addDet(Comparator.EQ, var1._length(), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_51_2() {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("a"), var1._subString(3,2));
		pc._addDet(Comparator.EQ, var1._length(), new IntegerConstant(4));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_51_3() {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("ab"), var1._subString(3,2));
		pc._addDet(Comparator.EQ, var1._length(), new IntegerConstant(4));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_52_1() {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("a"), var1._subString(3,2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(2)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_52_2() {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("a"), var1._subString(3,2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(2)), new IntegerConstant((int) 'b'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_52_3() {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("ab"), var1._subString(4,2));
		pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(3)), new IntegerConstant((int) 'a'));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_53_1 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(5,2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("abc")), new IntegerConstant(2));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_53_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(5,2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("ab")), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_53_3 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(5,2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc")), new IntegerConstant(3));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_53_4 () {
		callerName();

		//TODO Investigate why this is different then Test_1_49_4
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(5,2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("bc")), new IntegerConstant(6));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_53_5 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var1._subString(5,2));
		pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("def")), new IntegerConstant(6));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
	}
	
	@Test
	public void Test_1_54_1 () {
		callerName();

		//(stringvar0 startswith CONST_Z) && (stringvar0 startswith stringvar1) && (stringvar0 startswith CONST_8)
		
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var0 = new StringSymbolic("var0");
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("Z"), var0);
		stringCurrentPC._addDet(StringComparator.STARTSWITH, var1, var0);
		stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("8"), var0);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_54_2 () {
		callerName();

		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringSymbolic var0 = new StringSymbolic("var0");
		StringSymbolic var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("Z"), var0);
		stringCurrentPC._addDet(StringComparator.STARTSWITH, var1, var0);
		stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("8"), var0);
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}
	
	@Test
	public void Test_1_60_2() {
		callerName();

		//(CONST_nu notequals stringvar0) && (stringvar0 contains stringvar1) && (stringvar0 notcontains stringvar1)
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+symbolic.string_preprocess_only=true"};
		Config cfg = new Config(options);
		new SymbolicInstructionFactory(cfg);
		PathCondition pc = new PathCondition();
		StringPathCondition stringCurrentPC = new StringPathCondition(pc);
		StringExpression var0 = new StringSymbolic("var0");
		StringExpression var1 = new StringSymbolic("var1");
		stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var1, var0);
		stringCurrentPC._addDet(StringComparator.CONTAINS, var1, var0);
		stringCurrentPC._addDet(StringComparator.NOTEQUALS, var0, new StringConstant("nu"));
		System.out.println(stringCurrentPC);
		boolean result = stringCurrentPC.simplify();
		assertTrue(!result);
	}

	
	
}

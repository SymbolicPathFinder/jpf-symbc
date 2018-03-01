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
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringComparator;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringPathCondition;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;

import org.junit.Test;


public class TestNewAutomata extends TestJPF {
	@Test
	//NOTEQUALS
	public void Test1_1 () {
		String[] solvers = new String[]{"automata"};
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
	public void Test1_2 () {
		String[] solvers = new String[]{"automata"};
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
	public void Test1_3 () {
		String[] solvers = new String[]{"automata"};
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
	public void Test2_1 () {
		String[] solvers = new String[]{"automata"};
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
	public void Test3_1 () {
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(var2.solution().equals("cc"));
			assertTrue(var1.solution().trim().equals("cc"));
		}
	}
	
	@Test
	public void Test10_2 () {
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata"};
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
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
		/*
		 	"SYM_a"->"C_CONST_gLR" [label="StartsWith"]
			"C_CONST_kR"->"SYM_a" [label="!StartsWith"]
			"C_CONST_O4+]"->"SYM_a" [label="!StartsWith"]
		 */
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
		/*
		 	"SYM_b"->"C_CONST_Y&v^" [label="EndsWith"]
			"SYM_a"->"SYM_b" [label="!Equal", dir=both]
			"C_CONST_N@"->"SYM_b" [label="!EndsWith"]
		 */
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
		/*
		 	"SYM_b"->"C_CONST_9u" [label="StartsWith"]
			"SYM_a"->"C_CONST_9u" [label="EndsWith"]
			"SYM_a"->"SYM_b" [label="EdgeNotContains"]
		 */
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
		//(stringvar1 notequals stringvar0) && (stringvar0 endswith stringvar1) && (stringvar1 endswith CONST_M.m)
		
		String[] solvers = new String[]{"automata"};
		//String[] solvers = new String[]{"automata", "z3_inc"};
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
}

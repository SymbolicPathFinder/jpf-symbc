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

import javax.print.attribute.IntegerSyntax;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.util.test.TestJPF;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringComparator;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringPathCondition;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;

import org.junit.Test;


public class TestSymString extends TestJPF {

	String[] solvers = new String[]{"automata","z3" /* "z3_inc" */};
	
	@Test
	public void Test1 () {
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
			StringSymbolic var1 = new StringSymbolic("var1");
			StringExpression pre = var1;
			StringExpression var = pre._subString(3, 2);
			StringExpression constant1 = new StringConstant("test");
			StringExpression constant2 = new StringConstant("s");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, constant1, pre);
			stringCurrentPC._addDet(StringComparator.EQUALS, constant2, var);		
			boolean result = stringCurrentPC.simplify();
			assertTrue(result);
			assertTrue(!var1.solution().equals("test"));
			assertTrue(var1.solution().substring(2,3).equals("s"));
		}
	}
	
	@Test
	public void Test2_1 () {
		
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
	public void Test2_2 () {
		
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
	public void Test2_3 () {
		
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
	public void Test2_4 () {
		
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
	public void Test3_1 () {
		
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
	public void Test3_2 () {
		
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
	public void Test3_3 () {
		
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
	public void Test3_4 () {
		
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
	public void Test4_1 () {
		
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
	public void Test4_2 () {
		
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
	public void Test4_3 () {
		
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
	public void Test4_4 () {
		
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
	public void Test5_1 () {
		
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
	public void Test5_2 () {
		
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
	public void Test5_3 () {
		
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
	public void Test5_4 () {
		
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
	
	@Test
	public void Test6_1 () {
		
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
	public void Test6_2 () {
		
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
	public void Test6_3 () {
		
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
	public void Test6_4 () {
		
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
	public void Test6_5 () {
		
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
	public void Test6_6 () {
		
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
	public void Test6_7 () {
		
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
	public void Test6_8 () {
		
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
	
	@Test
	public void Test7_1 () {
		
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
	public void Test7_2 () {
		
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
	
	@Test
	//TODO: Could do with a speedup
	public void Test8_1 () {
		
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
	public void Test8_2 () {
		
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
	//TODO: Could do with a speedup
	public void Test9_1 () {
		
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
			pc._addDet(Comparator.GT, var1._indexOf(new IntegerConstant((int) 'a')), 0);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue("Solver " + solver + " failed",  !result);
			/*assertTrue(var1.solution().startsWith("aa"));
			assertTrue(var1.solution().indexOf("a") > 0);*/
			
		}
	}
	
	@Test
	public void Test9_2 () {
		
		
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
			pc._addDet(Comparator.GT, var1._indexOf(new IntegerConstant((int) 'a')), 0);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().startsWith("bb"));
			assertTrue(var1.solution().indexOf("a") > 0);
			
		}
	}
	
	@Test
	//TODO: Could do with a speedup
	public void Test10_1 () {
		
		
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
	public void Test10_2 () {
		
		
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
	public void Test11_1 () {
		
		
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
	public void Test12_1 () {
		
		
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
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), new IntegerConstant((int) 'a'));
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().charAt(1) == 'a');
			
		}
	}
	
	@Test
	public void Test12_2 () {
		
		
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
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(1)), new IntegerConstant((int) 'a'));
			boolean result = stringCurrentPC.simplify();
			System.out.println(pc);
			System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().charAt(1) != 'a');
		}
	}
	
	@Test
	public void Test13_1 () {
		
		
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
			SymbolicInteger si = new SymbolicInteger("si1");
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), si);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().charAt(1) == si.solution());
			
		}
	}
	
	@Test
	public void Test14_1 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var1, new StringConstant("abc"));
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var2, new StringConstant("b"));
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(!result);
		}
	}
	
	@Test
	public void Test14_2 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var1, new StringConstant("abc"));
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var2, new StringConstant("b"));
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(!var1.solution().equals(var2.solution()));
		}
	}
	
	@Test
	public void Test15_1 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(!var1.solution().equals(var2.solution()));
		}
	}
	
	@Test
	public void Test15_2 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().equals(var2.solution()));
		}
	}
	
	@Test
	public void Test16 () {
		
		
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
			StringExpression var2 = var1._trim();
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, new StringConstant("ab"));
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(result);
			assertTrue(var1.solution().trim().equals("ab"));
		}
	}
	
	@Test
	public void Test17 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant(" "), var1);
			StringExpression var2 = var1._trim();
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("ab"), var2 );
			//System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().trim().equals("ab"));
			assertTrue(var1.solution().startsWith(" "));
		}
	}
	
	@Test
	public void Test18 () {
		
		
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
			StringExpression var1ss = var1._subString(1);
			stringCurrentPC._addDet(StringComparator.EQUALS, var1ss, var2 );
			//System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().substring(1).equals(var2.solution()));
		}
	}
	
	@Test
	public void Test19_1 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("a"), var2 );
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var2, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().endsWith("a"));
			assertTrue(var1.solution().startsWith(var2.solution()));
		}
	}
	
	@Test
	public void Test19_2 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("a"), var2 );
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var2, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().endsWith("a"));
			assertTrue(var1.solution().startsWith(var2.solution()));
		}
	}
	
	@Test
	public void Test19_3 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("a"), var2 );
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var2, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().endsWith("a"));
			assertTrue(!var1.solution().startsWith(var2.solution()));
		}
	}
	
	@Test
	public void Test19_4 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("a"), var2 );
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, var2, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().endsWith("a"));
			assertTrue(!var1.solution().startsWith(var2.solution()));
		}
	}
	
	@Test
	public void Test20_1 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
		}
	}
	
	@Test
	public void Test20_2 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
		}
	}
	
	@Test
	public void Test20_3 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
		}
	}
	
	@Test
	public void Test20_4 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			System.out.printf("var1: '%s'\n", var1.solution());
			System.out.printf("var2: '%s'\n", var2.solution());
			System.out.printf("var3: '%s'\n", var3.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
		}
	}
	
	@Test
	public void Test21_1 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
			assertTrue(var3.solution().equals(var4.solution()));
		}
	}
	
	@Test
	public void Test21_2 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
			assertTrue(var3.solution().equals(var4.solution()));
		}
	}
	
	@Test
	public void Test21_3 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(var3.solution().equals(var4.solution()));
		}
	}
	
	@Test
	public void Test21_4 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(var3.solution().equals(var4.solution()));
		}
	}
	
	@Test
	public void Test21_5 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
		}
	}
	
	@Test
	public void Test21_6 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
		}
	}
	
	@Test
	public void Test21_7 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
		}
	}
	
	@Test
	public void Test21_8 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
		}
	}
	
	@Test
	public void Test22_1 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
			assertTrue(var3.solution().equals(var4.solution()));
			assertTrue(var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_2 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test22_3 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test22_4 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(var3.solution().equals(var4.solution()));
			assertTrue(var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_5 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test22_6 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
			assertTrue(var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_7 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
			assertTrue(var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_8 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
			assertTrue(var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_9 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test22_10 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
			assertTrue(var3.solution().equals(var4.solution()));
			assertTrue(!var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_11 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(var3.solution().equals(var4.solution()));
			assertTrue(!var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_12 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(var3.solution().equals(var4.solution()));
			assertTrue(!var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_13 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
			assertTrue(!var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_14 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
			assertTrue(!var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_15 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
			assertTrue(!var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test22_16 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, var3 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var4, var1 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().equals(var1.solution()));
			assertTrue(!var2.solution().equals(var3.solution()));
			assertTrue(!var3.solution().equals(var4.solution()));
			assertTrue(!var4.solution().equals(var1.solution()));
		}
	}
	
	@Test
	public void Test23 () {
		
		
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
			StringSymbolic var3 = new StringSymbolic("var3");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var2 );
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1 );
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var3, var2 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().equals(var1.solution()));
			assertTrue(var1.solution().startsWith("aa"));
			assertTrue(var2.solution().startsWith(var3.solution()));
		}
	}
	
	@Test
	public void Test24_1 () {
		
		
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
			StringExpression var3 = var1._concat(var2);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().concat(var2.solution()).equals("abc"));
		}
	}
	
	@Test
	public void Test24_2 () {
		
		
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
			StringExpression var3 = var1._concat(var2);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("abc"), var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().concat(var2.solution()).equals("abc"));
		}
	}
	
	@Test
	public void Test25_1 () {
		
		
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
			StringExpression var2 = new StringConstant("c");
			StringExpression var3 = var1._concat(var2);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().concat(var2.solution()).equals("abc"));
		}
	}
	
	@Test
	public void Test25_2 () {
		
		
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
			StringExpression var2 = new StringConstant("c");
			StringExpression var3 = var1._concat(var2);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("abc"), var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().concat(var2.solution()).equals("abc"));
		}
	}
	
	@Test
	public void Test26_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("a");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringExpression var3 = var1._concat(var2);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("abc"), var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().concat(var2.solution()).equals("abc"));
		}
	}
	
	@Test
	public void Test26_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("a");
			StringSymbolic var2 = new StringSymbolic("var2");
			StringExpression var3 = var1._concat(var2);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("abc"), var3 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().concat(var2.solution()).equals("abc"));
		}
	}
	
	@Test
	public void Test27_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("a");
			StringExpression var2 = new StringConstant("bc");
			StringExpression var3 = var1._concat(var2);
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.EQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var4.solution().equals("abc"));
		}
	}
	
	@Test
	public void Test27_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringConstant("a");
			StringExpression var2 = new StringConstant("bc");
			StringExpression var3 = var1._concat(var2);
			StringSymbolic var4 = new StringSymbolic("var4");
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var3, var4 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var4.solution().equals("abc"));
		}
	}
	
	@Test
	public void Test28_1 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1 );
			pc._addDet(Comparator.GT, var1._length(), 5);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("abc"));
			assertTrue(var1.solution().length() > 5);
		}
	}
	
	@Test
	public void Test28_2 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1 );
			pc._addDet(Comparator.GT, var1._length(), 5);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().startsWith("abc"));
			assertTrue(var1.solution().length() > 5);
		}
	}
	
	@Test
	public void Test28_3 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("abc"), var1 );
			pc._addDet(Comparator.LE, var1._length(), 5);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("abc"));
			assertTrue(var1.solution().length() <= 5);
		}
	}
	
	@Test
	public void Test28_4 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("abc"), var1 );
			pc._addDet(Comparator.LE, var1._length(), 5);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().startsWith("abc"));
			assertTrue(var1.solution().length() <= 5);
		}
	}
	
	@Test
	public void Test29_1 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(5)), (int) 'c');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(5) == 'c');
		}
	}
	
	@Test
	public void Test29_2 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(5)), (int) 'c');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(5) == 'c');
		}
	}
	
	@Test
	public void Test29_3 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(5)), (int) 'c');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(5) != 'c');
		}
	}
	
	@Test
	public void Test29_4 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(5)), (int) 'c');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(5) != 'c');
		}
	}
	
	@Test
	public void Test30_1 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(1) == 'a');
		}
	}
	
	@Test
	public void Test30_2 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(1)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(1) == 'a');
		}
	}
	
	@Test
	public void Test30_3 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(1)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test30_4 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(1)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(1) != 'a');
		}
	}
	
	@Test
	public void Test31_1 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1 );
			SymbolicInteger si = new SymbolicInteger("si1");
			pc._addDet(Comparator.EQ, var1._charAt(si), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(si.solutionInt()) == 'a');
		}
	}
	
	@Test
	public void Test31_2 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("aa"), var1 );
			SymbolicInteger si = new SymbolicInteger("si1");
			pc._addDet(Comparator.EQ, var1._charAt(si), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(si.solutionInt()) == 'a');
		}
	}
	
	@Test
	public void Test31_3 () {
		//assertTrue(false);
		
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("aa"), var1 );
			SymbolicInteger si = new SymbolicInteger("si1");
			pc._addDet(Comparator.NE, var1._charAt(si), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(si.solutionInt()) != 'a');
		}
	}
	
	@Test
	public void Test31_4 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("aa"), var1 );
			SymbolicInteger si = new SymbolicInteger("si1");
			pc._addDet(Comparator.NE, var1._charAt(si), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().startsWith("aa"));
			assertTrue(var1.solution().charAt(si.solutionInt()) != 'a');
		}
	}
	
	@Test
	public void Test32_1 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().endsWith("aa"));
			assertTrue(var1.solution().charAt(0) == 'a');
		}
	}
	
	@Test
	public void Test32_2 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().endsWith("aa"));
			assertTrue(var1.solution().charAt(0) == 'a');
		}
	}
	
	@Test
	public void Test32_3 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().endsWith("aa"));
			assertTrue(var1.solution().charAt(0) != 'a');
		}
	}
	
	@Test
	public void Test32_4 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("aa"), var1 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().endsWith("aa"));
			assertTrue(var1.solution().charAt(0) != 'a');
		}
	}
	
	@Test
	public void Test33_1 () {
		
		
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
			StringExpression var2 = var1._subString(5,3);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("aa"), var2 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().substring(3,5).equals("aa"));
		}
	}
	
	@Test
	public void Test33_2 () {
		
		
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
			StringExpression var2 = var1._subString(5,3);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("aa"), var2 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().substring(3,5).equals("aa"));
		}
	}
	
	@Test
	public void Test34_1 () {
		
		
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
			StringExpression var2 = var1._subString(5,3);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("aa"), var2 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().substring(3,5).equals("aa"));
			assertTrue(var1.solution().charAt(0) == 'a');
		}
	}
	
	@Test
	public void Test34_2 () {
		
		
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
			StringExpression var2 = var1._subString(5,3);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("aa"), var2 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().substring(3,5).equals("aa"));
			assertTrue(var1.solution().charAt(0) == 'a');
		}
	}
	
	@Test
	public void Test34_3 () {
		
		
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
			StringExpression var2 = var1._subString(5,3);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("aa"), var2 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().substring(3,5).equals("aa"));
			assertTrue(var1.solution().charAt(0) != 'a');
		}
	}
	
	@Test
	public void Test34_4 () {
		
		
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
			StringExpression var2 = var1._subString(5,3);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("aa"), var2 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().substring(3,5).equals("aa"));
			assertTrue(var1.solution().charAt(0) != 'a');
		}
	}
	
	@Test
	public void Test35_1 () {
		
		
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
			StringExpression var2 = var1._subString(3);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("aa"), var2 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().substring(3).equals("aa"));
		}
	}
	
	@Test
	public void Test35_2 () {
		
		
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
			StringExpression var2 = var1._subString(3);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("aa"), var2 );
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().substring(3).equals("aa"));
		}
	}
	
	@Test
	public void Test36_1 () {
		
		
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
			StringExpression var2 = var1._subString(3);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("aa"), var2 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().substring(3).equals("aa"));
			assertTrue(var1.solution().charAt(0) == 'a');
		}
	}
	
	@Test
	public void Test36_2 () {
		
		
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
			StringExpression var2 = var1._subString(3);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("aa"), var2 );
			pc._addDet(Comparator.EQ, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().substring(3).equals("aa"));
			assertTrue(var1.solution().charAt(0) == 'a');
		}
	}
	
	@Test
	public void Test36_3 () {
		
		
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
			StringExpression var2 = var1._subString(3);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("aa"), var2 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().substring(3).equals("aa"));
			assertTrue(var1.solution().charAt(0) != 'a');
		}
	}
	
	@Test
	public void Test36_4 () {
		
		
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
			StringExpression var2 = var1._subString(3);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, new StringConstant("aa"), var2 );
			pc._addDet(Comparator.NE, var1._charAt(new IntegerConstant(0)), (int) 'a');
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().substring(3).equals("aa"));
			assertTrue(var1.solution().charAt(0) != 'a');
		}
	}
	
	@Test
	public void Test37 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("hello"), var1);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("el")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test38_1 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("hello"), var1);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("el")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().endsWith("hello"));
			assertTrue(var1.solution().indexOf("el") == 2);
		}
	}
	
	@Test
	public void Test38_2 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("hello"), var1);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("el")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().endsWith("hello"));
			assertTrue(var1.solution().indexOf("el") == 2);
		}
	}
	
	@Test
	public void Test38_3 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("hello"), var1);
			pc._addDet(Comparator.NE, var1._indexOf(new StringConstant("el")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().endsWith("hello"));
			assertTrue(var1.solution().indexOf("el") != 2);
		}
	}
	
	@Test
	public void Test38_4 () {
		
		
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
			stringCurrentPC._addDet(StringComparator.NOTENDSWITH, new StringConstant("hello"), var1);
			pc._addDet(Comparator.NE, var1._indexOf(new StringConstant("el")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			//System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().endsWith("hello"));
			assertTrue(var1.solution().indexOf("el") != 2);
		}
	}
	
	@Test
	public void Test39_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = var1._subString(7, 2);
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, new StringConstant("hello"));
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("el")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", !result);
		}
	}

	@Test
	public void Test39_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = var1._subString(7, 2);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, new StringConstant("hello"));
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("el")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().substring(2,7).equals("hello"));
			assertTrue(var1.solution().indexOf("el") == 2);
		}
	}

	@Test
	public void Test39_3 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = var1._subString(7, 2);
			stringCurrentPC._addDet(StringComparator.EQUALS, var2, new StringConstant("hello"));
			pc._addDet(Comparator.NE, var1._indexOf(new StringConstant("el")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().substring(2,7).equals("hello"));
			assertTrue(var1.solution().indexOf("el") != 2);
		}
	}

	@Test
	public void Test39_4 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = var1._subString(7, 2);
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var2, new StringConstant("hello"));
			pc._addDet(Comparator.NE, var1._indexOf(new StringConstant("el")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().substring(2,7).equals("hello"));
			assertTrue(var1.solution().indexOf("el") != 2);
		}
	}
	
	@Test
	public void Test40_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			pc._addDet(Comparator.EQ, new StringConstant("hello")._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue("hello".indexOf(var1.solution()) == 2);
		}
	}
	
	@Test
	public void Test40_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			pc._addDet(Comparator.NE, new StringConstant("hello")._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue("hello".indexOf(var1.solution()) != 2);
		}
	}
	
	@Test
	public void Test41_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			pc._addDet(Comparator.EQ, new StringConstant("hello ")._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue("hello".indexOf(var1.solution()) == 2);
		}
	}
	
	@Test
	public void Test41_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			pc._addDet(Comparator.NE, new StringConstant("hello ")._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue("hello".indexOf(var1.solution()) != 2);
		}
	}
	
	@Test
	public void Test42_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.EQ, var2._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solution()) == 2);
		}
	}
	
	@Test
	public void Test42_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.EQ, var2._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			System.out.println(String.format("var1.solution(): '%s'", var1.solution()));
			System.out.println(String.format("var2.solution(): '%s'", var2.solution()));
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solution()) == 2);
		}
	}
	
	@Test
	public void Test42_3 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.NE, var2._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solution()) != 2);
		}
	}
	
	@Test
	public void Test42_4 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.NE, var2._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solution()) != 2);
		}
	}
	
	/*
	 * Slow automata
	 */
	//@Test
	public void remTest43 () {
		String[] solvers = new String[]{"automata", "z3_inc"};
		
		for (String solver: solvers) {
			long startTime = System.currentTimeMillis();
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			
			StringSymbolic var[] = new StringSymbolic[25];
			for (int i = 0; i < var.length; i++) {
				var[i] = new StringSymbolic ("var" + i);
				pc._addDet(Comparator.EQ, var[i]._length(), new IntegerConstant(20));
			}
			
			for (int i = 0; i < var.length; i++) {
				StringBuffer sb = new StringBuffer();
				for (char j = 'a'; j < 'a' + 25; j++) {
					sb.append (j);
				}
				stringCurrentPC._addDet(StringComparator.STARTSWITH, var[i], new StringConstant(sb.toString()));
			}
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			System.out.println(solver + " " + (System.currentTimeMillis() - startTime));
		}
	}
	
	//@Test
	public void remTest44 () {
		String[] solvers = new String[]{"automata", "z3_inc"};
		
		for (String solver: solvers) {
			long startTime = System.currentTimeMillis();
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			
			StringSymbolic var[] = new StringSymbolic[25];
			//StringSymbolic var[] = new StringSymbolic[5];
			for (int i = 0; i < var.length; i++) {
				var[i] = new StringSymbolic ("var" + i);
				pc._addDet(Comparator.EQ, var[i]._length(), new IntegerConstant(30));
				//pc._addDet(Comparator.EQ, var[i]._length(), new IntegerConstant(5));
				stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant(String.valueOf((char) (i + 'a'))), var[i]);
			}
			
			for (int i = 0; i < var.length-1; i++) {
				stringCurrentPC._addDet(StringComparator.NOTCONTAINS, var[i], var[i+1]);
			}
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			System.out.println(solver + " " + (System.currentTimeMillis() - startTime));
		}
	}
	
	@Test
	public void Test45_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().contains("a"));
		}
	}
	
	@Test
	public void Test45_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().contains("a"));
		}
	}
	
	@Test
	public void Test46_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			pc._addDet(Comparator.LE, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().contains("a"));
			assertTrue(var1.solution().length() <= 3);
		}
	}
	
	@Test
	public void Test46_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			pc._addDet(Comparator.LE, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().contains("a"));
			assertTrue(var1.solution().length() <= 3);
		}
	}
	
	@Test
	public void Test46_3 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("a"), var1);
			pc._addDet(Comparator.GT, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().contains("a"));
			assertTrue(var1.solution().length() > 3);
		}
	}
	
	@Test
	public void Test46_4 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("a"), var1);
			pc._addDet(Comparator.GT, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().contains("a"));
			assertTrue(var1.solution().length() > 3);
		}
	}
	
	@Test
	public void Test47_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("hello"), var1);
			pc._addDet(Comparator.LE, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test47_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("hello"), var1);
			pc._addDet(Comparator.GT, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().contains("hello"));
			assertTrue(var1.solution().length() > 3);
		}
	}
	
	@Test
	public void Test47_3 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("hello"), var1);
			pc._addDet(Comparator.LE, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var1.solution().contains("hello"));
			assertTrue(var1.solution().length() <= 3);
		}
	}
	
	@Test
	public void Test47_4 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("hello"), var1);
			pc._addDet(Comparator.GT, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(!var1.solution().contains("hello"));
			assertTrue(var1.solution().length() > 3);
		}
	}
	
	@Test
	public void Test48_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, var1, new StringConstant("hello"));
			pc._addDet(Comparator.LE, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue("hello".contains(var1.solution()));
			assertTrue(var1.solution().length() <= 3);
		}
	}
	
	@Test
	public void Test48_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.CONTAINS, var1, new StringConstant("hello"));
			pc._addDet(Comparator.GT, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue("hello".contains(var1.solution()));
			assertTrue(var1.solution().length() > 3);
		}
	}
	
	@Test
	public void Test48_3 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("hello"), var1);
			pc._addDet(Comparator.LE, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!"hello".contains(var1.solution()));
			assertTrue(var1.solution().length() <= 3);
		}
	}
	
	@Test
	public void Test48_4 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.NOTCONTAINS, new StringConstant("hello"), var1);
			pc._addDet(Comparator.GT, var1._length(), 3);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			System.out.printf("var1: '%s'\n", var1.solution());
			assertTrue(!"hello".contains(var1.solution()));
			assertTrue(var1.solution().length() > 3);
		}
	}
	
	@Test
	public void Test49_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			pc._addDet(Comparator.GT, var1._length(), 3);
			pc._addDet(Comparator.LT, var2._length(), 2);
			stringCurrentPC._addDet(StringComparator.CONTAINS, var1, var2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test49_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			pc._addDet(Comparator.LT, var1._length(), 3);
			pc._addDet(Comparator.GT, var2._length(), 2);
			stringCurrentPC._addDet(StringComparator.CONTAINS, var1, var2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().contains(var1.solution()));
			assertTrue(var1.solution().length() < 3);
			assertTrue(var2.solution().length() > 2);
		}	
	}
	
	@Test
	public void Test50 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, new StringConstant("aaa"));
			stringCurrentPC._addDet(StringComparator.NOTEQUALS, var1, new StringConstant("aaa"));
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test51 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("a"), var1);
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("b"), var1);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test52 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("ab"), var1);
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("ab"), var1);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("ab"));
			assertTrue(var1.solution().endsWith("ab"));
		}
	}
	
	@Test
	public void Test53_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("c"), var1);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("d")), -1);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("c"));
			assertTrue(var1.solution().indexOf("d") == -1);
		}
	}
	
	@Test
	public void Test53_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("c"), var1);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("d")), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith("c"));
			assertTrue(var1.solution().indexOf("d") == 2);
		}
	}
	
	@Test
	public void Test54 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("c"), var1);
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("d"), var1);
			pc._addDet(Comparator.EQ, var1._indexOf(new StringConstant("d")), -1);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", !result);
		}
	}
	
	@Test
	public void Test55 () {
		
		//String[] solvers = new String[]{"z3"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant(" "), var1);
			stringCurrentPC._addDet(StringComparator.STARTSWITH, var2, var1);
			stringCurrentPC._addDet(StringComparator.ENDSWITH, new StringConstant("c"), var1);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("ab"), var2._trim());
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var1.solution().startsWith(" "));
			assertTrue(var1.solution().startsWith(var2.solution()));
			assertTrue(var1.solution().endsWith("c"));
			assertTrue(var2.solution().trim().equals("ab"));
		}
	}
	
	@Test
	public void Test56 () {
		
		//String[] solvers = new String[]{"z3"};
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			StringExpression var3 = var1._concat(var2);
			stringCurrentPC._addDet(StringComparator.EQUALS, new StringConstant("hello"), var3._subString(new IntegerConstant(2)));
			stringCurrentPC._addDet(StringComparator.EQUALS, var1, var3._subString(new IntegerConstant(2), new IntegerConstant(0)));
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var3.solution().substring(2).equals("hello"));
			assertTrue(var3.solution().substring(0,2).equals(var1.solution()));
		}
	}
	
	@Test
	public void Test57_1 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.EQ, var2._indexOf(var1, new IntegerConstant(0)), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solution()) == 2);
		}
	}
	
	@Test
	public void Test57_2 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.EQ, var2._indexOf(var1, new IntegerConstant(0)), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			System.out.println(String.format("var1.solution(): '%s'", var1.solution()));
			System.out.println(String.format("var2.solution(): '%s'", var2.solution()));
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().startsWith("bol"));
//			assertTrue(var2.solution().indexOf(var1.solution()) == 2);
			assertTrue(var2.solution().indexOf(var1.solution(),2) == 2);
		}
	}
	
	@Test
	public void Test57_3 () {
		
		
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.NE, var2._indexOf(var1, new IntegerConstant(0)), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solution()) != 2);
		}
	}
	
	@Test
	public void Test57_4 () {
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression var1 = new StringSymbolic("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.NE, var2._indexOf(var1, new IntegerConstant(0)), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solution()) != 2);
		}
	}
	
	@Test
	public void Test58_1 () {
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			SymbolicInteger var1 = new SymbolicInteger("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.EQ, var2._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solutionChar()) == 2);
		}
	}
	
	@Test
	public void Test58_2 () {
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			SymbolicInteger var1 = new SymbolicInteger("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.EQ, var2._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			System.out.println(String.format("var1.solution(): '%s'", var1.solution()));
			System.out.println(String.format("var2.solution(): '%s'", var2.solution()));
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solutionInt()) == 2);
		}
	}
	
	@Test
	public void Test58_3 () {
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			SymbolicInteger var1 = new SymbolicInteger("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.NE, var2._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solutionInt()) != 2);
		}
	}
	
	@Test
	public void Test58_4 () {
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			SymbolicInteger var1 = new SymbolicInteger("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.NE, var2._indexOf(var1), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solutionInt()) != 2);
		}
	}
	
	@Test
	public void Test59_1 () {
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			SymbolicInteger var1 = new SymbolicInteger("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.EQ, var2._indexOf(var1, new IntegerConstant(0)), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solutionInt()) == 2);
		}
	}
	
	@Test
	public void Test59_2 () {
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			SymbolicInteger var1 = new SymbolicInteger("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.EQ, var2._indexOf(var1, new IntegerConstant(0)), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			System.out.println(String.format("var1.solution(): '%s'", var1.solution()));
			System.out.println(String.format("var2.solution(): '%s'", var2.solution()));
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solutionChar()) == 2);
		}
	}
	
	@Test
	public void Test59_3 () {
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			SymbolicInteger var1 = new SymbolicInteger("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.NE, var2._indexOf(var1, new IntegerConstant(0)), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solutionChar()) != 2);
		}
	}
	
	@Test
	public void Test59_4 () {
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			SymbolicInteger var1 = new SymbolicInteger("var1");
			StringExpression var2 = new StringSymbolic("var2");
			stringCurrentPC._addDet(StringComparator.NOTSTARTSWITH, new StringConstant("bol"), var2);
			pc._addDet(Comparator.NE, var2._indexOf(var1, new IntegerConstant(0)), 2);
			System.out.println(stringCurrentPC);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(!var2.solution().startsWith("bol"));
			assertTrue(var2.solution().indexOf(var1.solutionChar()) != 2);
		}
	}
	
	@Test
	//MS_Example
	public void Test60_1 () {	
		for (String solver: solvers) {
			System.out.println("Solver: " + solver);
			String[] options = {"+symbolic.dp=choco",
					"+symbolic.string_dp=" + solver,
					"+symbolic.string_dp_timeout_ms=0"};
			Config cfg = new Config(options);
			new SymbolicInstructionFactory(cfg);
			PathCondition pc = new PathCondition();
			StringPathCondition stringCurrentPC = new StringPathCondition(pc);
			StringExpression str = new StringSymbolic("str");
			IntegerExpression ie1 = str._lastIndexOf(new IntegerConstant('/'));
			pc._addDet(Comparator.GE, ie1, new IntegerConstant(0));
			StringExpression rest = str._subString(ie1._plus(1));
			stringCurrentPC._addDet(StringComparator.CONTAINS, new StringConstant("EasyChair"), rest);
			stringCurrentPC._addDet(StringComparator.STARTSWITH, new StringConstant("http://"), str);
			boolean result = stringCurrentPC.simplify();
			assertTrue(solver + " failed", result);
			assertTrue(str.solution().lastIndexOf('/') >= 0);
			assertTrue(str.solution().substring(ie1.solutionInt() + 1).contains("EasyChair"));
			assertTrue(str.solution().startsWith("http://"));
		}
	}
	
	

}

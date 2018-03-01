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
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
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


public class TestSymStringPreprocessing extends TestJPF {

	String[] solvers = new String[]{"automata", "z3_inc"};
	
	@Test
	public void Test1_1 () {
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
	public void Test1_2 () {
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
	public void Test1_3 () {
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
	public void Test1_4 () {
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
	public void Test2_1 () {
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
	public void Test2_2 () {
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
	public void Test2_3 () {
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
	public void Test2_4 () {
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
	public void Test3_1 () {
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
	public void Test3_2 () {
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
	public void Test3_3 () {
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
	public void Test3_4 () {
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
	public void Test4_1 () {
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
	public void Test4_2 () {
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
	public void Test4_3 () {
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
	public void Test4_4 () {
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
	public void Test5_1 () {
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
	public void Test5_2 () {
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
	public void Test5_3 () {
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
	public void Test5_4 () {
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
	public void Test5_5 () {
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
	public void Test5_6 () {
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
	public void Test5_7 () {
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
	public void Test5_8 () {
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
	public void Test6_1 () {
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
	public void Test6_2 () {
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
	public void Test6_3 () {
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
	public void Test6_4 () {
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
	public void Test6_5 () {
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
	public void Test6_6 () {
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
	public void Test6_7 () {
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
	public void Test6_8 () {
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
	public void Test7_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test7_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test8_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test8_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test9_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test9_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test10_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test10_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test11_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test11_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test12_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test12_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test13_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test13_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test14_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test14_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test15_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test15_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test15_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test15_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test16_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test16_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test16_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test16_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test17_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test17_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test17_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test18_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test18_3 () {
		//TODO: Improve
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test18_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test18_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test18_6 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test19_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test19_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test19_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test19_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test19_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test19_6 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test20_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test20_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test20_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test21_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test21_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test21_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test22_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test22_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test23_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test23_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test23_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test23_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test23_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test24_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test24_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test25_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test25_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test25_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test25_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test26_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test26_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test26_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test26_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test27_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test27_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test27_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test28_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test28_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test28_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test29_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test29_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test29_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test29_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test29_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test30_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test30_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test30_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test30_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test31_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test31_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test32_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test32_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test32_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test33_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test33_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test33_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test33_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test33_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test33_6 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_6 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_7 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_8 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_9 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_10 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_11 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_12 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test34_13 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test35_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test35_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test35_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test36_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test36_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test36_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test37_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test37_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test37_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test38_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test38_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test38_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test39_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test39_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test40_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test40_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test40_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test40_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test41_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test42_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test42_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test42_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test42_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test43_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test43_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test43_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test43_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test44_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test44_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test44_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test45_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test45_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test46_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test46_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test47_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test47_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test48_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test48_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test48_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test48_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test49_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test49_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test49_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test49_4 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test49_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test50_1() {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test50_2() {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test50_3() {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test51_1() {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test51_2() {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test51_3() {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test52_1() {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test52_2() {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test52_3() {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test53_1 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test53_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test53_3 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test53_4 () {
		//TODO Investigate why this is different then Test49_4
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test53_5 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test54_1 () {
		//(stringvar0 startswith CONST_Z) && (stringvar0 startswith stringvar1) && (stringvar0 startswith CONST_8)
		
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test54_2 () {
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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
	public void Test60_2() {
		//(CONST_nu notequals stringvar0) && (stringvar0 contains stringvar1) && (stringvar0 notcontains stringvar1)
		String[] options = {"+symbolic.dp=choco",
				"+symbolic.string_dp=automata",
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

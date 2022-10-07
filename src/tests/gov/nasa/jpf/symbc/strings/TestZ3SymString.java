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


public class TestZ3SymString extends TestJPF {

	String[] solvers = new String[]{"z3str3"};
	
	@Test
	public void Test1 () {
		for (String solver: solvers) {
			String[] options = {"+symbolic.dp=z3",
					"+symbolic.string_dp=" + solver,
					"+symbolic.strings=true",
					"+symbolic.debug=true",
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
			assertTrue(!stringCurrentPC.solution.get(var1.getName()).equals("test"));
			assertTrue(stringCurrentPC.solution.get(var1.getName()).substring(2,3).equals("s"));
		}
	}
}

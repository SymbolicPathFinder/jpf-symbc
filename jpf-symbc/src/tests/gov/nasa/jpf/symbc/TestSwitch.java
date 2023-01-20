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

package gov.nasa.jpf.symbc;

import org.junit.Test;


public class TestSwitch extends InvokeTest{
	public enum Y {Y1, Y2};
	
	void testSwitch1() {
		Y y = Y.Y1;
//		int x = 1;
//
//		switch (x) {
//		case 1: System.out.println(1); break;
//		case 2: System.out.println(2); break;
//		default: System.out.println("default: "); break;
//		}
		switch (y) {
//		case Y1: System.out.println(1); break;
		case Y2: System.out.println(2); break;
		default: System.out.println("default: "); break;
		}
	}

  private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.TestSwitch.testSwitch1()";
  private static final String[] JPF_ARGS = {INSN_FACTORY, SYM_METHOD};

  public static void main(String[] args) {
    runTestsOfThisClass(args);
  }

  @Test
  public void mainTest() {
    if (verifyNoPropertyViolation(JPF_ARGS)) {
      TestSwitch test = new TestSwitch();
      test.testSwitch1();
    }
  }

}

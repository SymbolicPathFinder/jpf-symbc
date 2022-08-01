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

public class TestBooleanSpecial1 extends BooleanTest {

  private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.TestBooleanSpecial1.testBooleanInvokeSpecial(sym#sym)";
  private static final String[] JPF_ARGS = {INSN_FACTORY, SYM_METHOD};

  public static void main(String[] args) {
    runTestsOfThisClass(args);
  }

  @Test
  public void mainTest() {
    if (verifyNoPropertyViolation(JPF_ARGS)) {
      TestBooleanSpecial1 test = new TestBooleanSpecial1();
      test.testBooleanInvokeSpecial(true, false);
    }
  }

  // "private" forces calls to use INVOKESPECIAL
  private void testBooleanInvokeSpecial(boolean x, boolean y) {
    testBoolean(x, y);
  }
}

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
import gov.nasa.jpf.util.test.TestJPF;
import org.junit.Test;
//import org.junit.runner.JUnitCore;

public class TestSymbolicJPF extends TestJPF {
  
  static final String TEST_CLASS = "gov.nasa.jpf.numeric.TestSymbolic";
  static final String NO_TRACE = "+jpf.report.console.property_violation=error";
  static final String INSN_FACTORY = "+vm.insn_factory.class=gov.nasa.jpf.symbc.SymbolicInstructionFactory";
  static final String STORAGE = "+vm.storage.class= ";
  
  public static void main(String args[]) {
      //JUnitCore.main(TEST_CLASS + "JPF");
  }
  
  //------------- IADD
  @Test
  public void testIADD_bothSymbolic () {
    String[] args = { STORAGE, NO_TRACE, INSN_FACTORY, TEST_CLASS, "testIADD_bothSymbolic" };
    verifyNoPropertyViolation(args);
  }

  @Test
  public void testIADD_oneConcrete () {
    String[] args = { STORAGE, NO_TRACE, INSN_FACTORY, TEST_CLASS, "testIADD_oneConcrete" };
    verifyNoPropertyViolation(args);
  }
  //------------- ISUB
  @Test
  public void testISUB_bothSymbolic () {
    String[] args = { STORAGE, NO_TRACE, INSN_FACTORY, TEST_CLASS, "testISUB_bothSymbolic" };
    verifyNoPropertyViolation(args);
  }

  @Test
  public void testISUB_oneConcrete () {
    String[] args = { STORAGE, NO_TRACE, INSN_FACTORY, TEST_CLASS, "testISUB_oneConcrete" };
    verifyNoPropertyViolation(args);
  }
}

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

public class InvokeTest extends TestJPF {

  protected static final String INSN_FACTORY = "+jvm.insn_factory.class=gov.nasa.jpf.symbc.SymbolicInstructionFactory";

  protected static String makePCAssertString(String location, String goodPC, String badPC) {
    return String.format("Bad Path condition in %s:\nEXPECTED:\n%s\nACTUAL:\n%s\n", location, goodPC, badPC);
  }

  protected static String trimPC(String pc) {
    return pc.substring(pc.indexOf("\n") + 1);
  }

  // Check whether the current PatchPathcondition looks like "# = 1\n <newPC> && <oldPC>"
  protected static boolean pcMatches(String newPC) {
    String currentPC = TestUtils.getPathCondition();
    currentPC = trimPC(currentPC);
    newPC = trimPC(newPC);
    return newPC.equals(currentPC);
  }

  protected static String joinPC(String pc, String oldPC) {
    pc = trimPC(pc);
    oldPC = trimPC(oldPC);
    if (oldPC.length() > 0) {
      return pc + " && " + oldPC;
    }
    return pc;
  }
}

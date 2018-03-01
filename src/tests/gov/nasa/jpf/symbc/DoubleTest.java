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

public class DoubleTest extends InvokeTest {

  // x > 1.1
  protected static String PC1 = "# = 1\nx_1_SYMREAL > CONST_1.1";
  //
  // (x <= 1.1)
  protected static String PC2 = "x_1_SYMREAL < CONST_1.1";
  protected static String PC10 = "x_1_SYMREAL > CONST_1.1";
  protected static String PC3 = "CONST_1.1 == x_1_SYMREAL";
  //
  // [(x > 1.1) && ((z := y) > 30.0)] || [(x < 1.1) && ((z := x+y) > 30.0)] || [(x == 1.1) && ((z := x+y) > 30.0)]
  protected static String PC4 = "(x_1_SYMREAL + y_2_SYMREAL) > CONST_30.0";
  protected static String PC5 = "y_2_SYMREAL > CONST_30.0";
  //
  // [((z := x+y) < 30.0) && (x == 1.1)] || [(x < 1.1) && ((z := x+y) < 30.0)] ||
  // [(x < 1.1) && ((z := x+y) == 30.0)] || [(x == 1.1) && ((z := x+y) == 30.0)] ||
  // [(x > 1.1) && ((z := y) < 30.0)] || [(x > 1.1) && ((z := y) == 30.0)]
  protected static String PC6 = "CONST_30.0 == (x_1_SYMREAL + y_2_SYMREAL)";
  protected static String PC7 = "(x_1_SYMREAL + y_2_SYMREAL) < CONST_30.0";
  protected static String PC8 = "y_2_SYMREAL < CONST_30.0";
  protected static String PC9 = "CONST_30.0 == y_2_SYMREAL";

  protected static void testDouble(double x, double y) {
    double z = x + y;

    if (x > 1.1) {
      assert pcMatches(PC1) : makePCAssertString("TestDoubleSpecial1.testDouble1 if x > 1.1", PC1, TestUtils.getPathCondition());
      z = y;
    } else {
      assert (pcMatches(PC2) || pcMatches(PC3)) : makePCAssertString("TestDoubleSpecial1.testDouble1 x <= 1.1",
              "either\n" + PC2 + "\nor\n" + PC3, TestUtils.getPathCondition());
    }
    String pc = TestUtils.getPathCondition();
    if (z > 30.0) {
      assert (pcMatches(joinPC(PC4, pc)) || pcMatches(joinPC(PC5, pc))) : makePCAssertString(
              "TestDoubleSpecial1.testDouble1 z > 30.0", "one of\n" + PC4 + "\nor\n"
              + PC5, TestUtils.getPathCondition());
      z = 91.0;
    } else {
      assert (pcMatches(PC2)) || pcMatches(PC3) || pcMatches(PC10) : makePCAssertString(
              "TestDoubleSpecial1.testDouble1 z <= 30.0", "one of \n" + PC2 + "\nor\n" + PC3 + "\nor\n" + PC10,
              TestUtils.getPathCondition());
    }
  }
}

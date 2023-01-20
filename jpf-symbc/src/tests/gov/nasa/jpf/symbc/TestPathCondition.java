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

public class TestPathCondition extends InvokeTest{

	// ------------------------ test1(float, float) -----------------------------

	// x > 1.1f
	private static String PC1 = "# = 1\nx_1_SYMREAL > CONST_1.100000023841858";

	//
	// (x <= 1.1f)
	private static String PC2 = "# = 1\nx_1_SYMREAL < CONST_1.100000023841858";

	private static String PC3 = "# = 1\nCONST_1.100000023841858 == x_1_SYMREAL";

	//
	// [(x > 1.1f) && ((z := y) > 30.0f)] || [(x < 1.1f) && ((z := x+y) > 30.0f)] || [(x == 1.1f) && ((z := x+y) > 30.0f)]
	private static String PC4 = "# = 2\n(x_1_SYMREAL + y_2_SYMREAL) > CONST_30.0 && CONST_1.100000023841858 == x_1_SYMREAL";

	private static String PC5_5 = "# = 2\ny_2_SYMREAL > CONST_30.0 && x_1_SYMREAL > CONST_1.100000023841858";

	private static String PC5_75 = "# = 2\n(x_1_SYMREAL + y_2_SYMREAL) > CONST_30.0 && x_1_SYMREAL < CONST_1.100000023841858";

	// private static String PC5_75 = "# = 2\n(x_1_SYMREAL + y_2_SYMREAL) > CONST_30.0 && x_1_SYMREAL < CONST_1.100000023841858";

	//
	// [((z := x+y) < 30.0f) && (x == 1.1f)] || [(x < 1.1f) && ((z := x+y) < 30.0f)] ||
	// [(x < 1.1f) && ((z := x+y) == 30.0f)] || [(x == 1.1f) && ((z := x+y) == 30.0f)] ||
	// [(x > 1.1f) && ((z := y) < 30.0f)] || [(x > 1.1f) && ((z := y) == 30.0f)]
	private static String PC6 = "# = 2\n(x_1_SYMREAL + y_2_SYMREAL) < CONST_30.0 && CONST_1.100000023841858 == x_1_SYMREAL";

	private static String PC6_5 = "# = 2\nCONST_30.0 == (x_1_SYMREAL + y_2_SYMREAL) && CONST_1.100000023841858 == x_1_SYMREAL";

	private static String PC6_75 = "# = 2\nCONST_30.0 == (x_1_SYMREAL + y_2_SYMREAL) && x_1_SYMREAL < CONST_1.100000023841858";

	// private static String PC6_75 = "# = 2\nCONST_30.0 == (x_1_SYMREAL + y_2_SYMREAL) && x_1_SYMREAL < CONST_1.100000023841858";

	private static String PC7 = "# = 2\n(x_1_SYMREAL + y_2_SYMREAL) < CONST_30.0 && x_1_SYMREAL < CONST_1.100000023841858";

	// private static String PC7 = "# = 2\n(x_1_SYMREAL + y_2_SYMREAL) < CONST_30.0 && x_1_SYMREAL < CONST_1.100000023841858";

	private static String PC8 = "# = 2\ny_2_SYMREAL < CONST_30.0 && x_1_SYMREAL > CONST_1.100000023841858";

	private static String PC9 = "# = 2\nCONST_30.0 == y_2_SYMREAL && x_1_SYMREAL > CONST_1.100000023841858";

	// "private" forces calls to use INVOKESPECIAL
	private void test1(float x, float y) {
		float z = x + y;
		// float z = 0.0f;
		// z = z / y;
		if (x > 1.1f) {
			assert PC1.equals(TestUtils.getPathCondition()) : makePCAssertString("TestDoubleSpecial.test1 if x > 1.1f",
					PC1, TestUtils.getPathCondition());
			z = y;
		} else {
			assert (PC2.equals(TestUtils.getPathCondition()) || PC3.equals(TestUtils.getPathCondition())) : makePCAssertString(
					"TestDoubleSpecial.test1 x <= 1.1f", "either\n" + PC2 + "\nor\n" + PC3, TestUtils
							.getPathCondition());
		}
		if (z > 30.0f) {
			assert (PC4.equals(TestUtils.getPathCondition()) || PC5_5.equals(TestUtils.getPathCondition()) || PC5_75
					.equals(TestUtils.getPathCondition())) : makePCAssertString("TestDoubleSpecial.test1 z > 30.0f",
					"one of\n" + PC4 + "\nor\n" + PC5_5 + "\nor\n" + PC5_75, TestUtils.getPathCondition());
			z = 91.0f; // Array out of bounds exception
		} else {
			assert (PC6.equals(TestUtils.getPathCondition()) || PC6_5.equals(TestUtils.getPathCondition())
					|| PC6_75.equals(TestUtils.getPathCondition()) || PC7.equals(TestUtils.getPathCondition())
					|| PC8.equals(TestUtils.getPathCondition()) || PC9.equals(TestUtils.getPathCondition())) : makePCAssertString(
					"TestDoubleSpecial.test1 z <= 30.0f", "one of\n" + PC6 + "\nor\n" + PC6_5 + "\nor\n" + PC6_75
							+ "\nor\n" + PC7 + "\nor\n" + PC8 + "\nor\n" + PC9, TestUtils.getPathCondition());
		}
		z = x * z;
		z = -z;
		// z = z % 3.0f;
		z = z - y;
	}

	// ------------------------ test2_concrete(double, double) -----------------------------
	// Same as test2_sym except called with concrete args, so Path Condition doesn't change.
	// "private" forces calls to use INVOKESPECIAL
	private void test2_concrete(double x2, double y2) {
		String prevPC = TestUtils.getPathCondition();
		System.out.println(">>>>> PREV PC: '" + prevPC + "'");
		double z = x2 + y2;
		// double z = 0.0;
		// z = z / y2;
		if (x2 > 1.1) {
			// assert PC2_1.equals(TestUtils.getPathCondition()) || PC2_1_5.equals(TestUtils.getPathCondition()) || PC2_1_5.equals(TestUtils.getPathCondition()) :
			// makePCAssertString("TestDoubleSpecial.test2_concrete if x2 > 1.1",
			// "one of\n" + PC2_1 + "\nor\n" + PC2_1_5 + "\nor\n" + PC2_1_5, TestUtils.getPathCondition());
			assert prevPC.equals(TestUtils.getPathCondition()) : makePCAssertString(
					"TestDoubleSpecial.test2_concrete if x2 > 1.1", prevPC, TestUtils.getPathCondition());
			z = y2; // BinaryRealExpression / IntegerExpression class cast exception
		} else {
			// assert (PC2_2.equals(TestUtils.getPathCondition()) || PC2_3.equals(TestUtils.getPathCondition())) : makePCAssertString(
			// "TestDoubleSpecial.test2_concrete x2 <= 1.1f", "either\n" + PC2_2 + "\nor\n" + PC2_3, TestUtils
			// .getPathCondition());
			assert prevPC.equals(TestUtils.getPathCondition()) : makePCAssertString(
					"TestDoubleSpecial.test2_concrete x2 <= 1.1f", prevPC, TestUtils.getPathCondition());
		}
		if (z > 30.0)
			z = 91.0; // BinaryRealExpression / IntegerExpression class cast exception
		z = x2 * z;
		z = -z;
		// z = z % 3;
		z = z - y2;
	}

	// ------------------------ test2_sym(double, double) -----------------------------
	// Same as test2_concrete except called with symbolic args, so Path Condition changes inside the "if" statements.
	private static String PC_TEST2_1 = "# = 3\nu_3_SYMREAL > CONST_1.1 && ";
	private static String PC_TEST2_2 = "# = 3\nCONST_1.1 == u_3_SYMREAL && ";
	private static String PC_TEST2_3 = "# = 3\nu_3_SYMREAL < CONST_1.1 && ";
	
	// "private" forces calls to use INVOKESPECIAL
	private void test2_sym(double x2, double y2) {
		String prevPC = TestUtils.getPathCondition().substring(6);
		System.out.println(">>>>> PREV PC: '" + prevPC + "'");
		double z = x2 + y2;
		// double z = 0.0;
		// z = z / y2;
		if (x2 > 1.1) {
			// assert PC2_1.equals(TestUtils.getPathCondition()) || PC2_1_5.equals(TestUtils.getPathCondition()) || PC2_1_5.equals(TestUtils.getPathCondition()) :
			// makePCAssertString("TestDoubleSpecial.test2_sym if x2 > 1.1",
			// "one of\n" + PC2_1 + "\nor\n" + PC2_1_5 + "\nor\n" + PC2_1_5, TestUtils.getPathCondition());
			assert (PC_TEST2_1 + prevPC).equals(TestUtils.getPathCondition()) : makePCAssertString(
					"TestDoubleSpecial.test2_sym if x2 > 1.1", PC_TEST2_1 + prevPC, TestUtils.getPathCondition());
			z = y2; // BinaryRealExpression / IntegerExpression class cast exception
		} else {
			// assert (PC2_2.equals(TestUtils.getPathCondition()) || PC2_3.equals(TestUtils.getPathCondition())) : makePCAssertString(
			// "TestDoubleSpecial.test2_sym x2 <= 1.1f", "either\n" + PC2_2 + "\nor\n" + PC2_3, TestUtils
			// .getPathCondition());
			assert (PC_TEST2_2 + prevPC).equals(TestUtils.getPathCondition()) || (PC_TEST2_3 + prevPC).equals(TestUtils.getPathCondition()) : makePCAssertString(
					"TestDoubleSpecial.test2_sym x2 <= 1.1f", "either\n" + PC_TEST2_2 + prevPC + "\nor\n" + PC_TEST2_3 + prevPC, TestUtils.getPathCondition());
		}
		if (z > 30.0)
			z = 91.0; // BinaryRealExpression / IntegerExpression class cast exception
		z = x2 * z;
		z = -z;
		// z = z % 3;
		z = z - y2;
	}

	private void test3_concrete(double x3, double y3) {
		String prevPC = TestUtils.getPathCondition();
		if (x3 > 2.2) {
			assert prevPC.equals(TestUtils.getPathCondition()) : makePCAssertString(
					"TestDoubleSpecial.test3 if x3 > 1.1", prevPC, TestUtils.getPathCondition());
		}
	}

	/**
	 * @param args
	 */
	public void test(float x, float y, double u, double v, int s, int t) {
    test1(x, y);
		test2_concrete(11.0, 21.0);
		test2_sym(u,v);
		test3_concrete(11.0, 21.0);
	}

	public static void main(String[] args) {
    runTestsOfThisClass(args);
	}

  private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.TestPathCondition.test(sym#sym#sym#sym#sym#sym)";
  private static final String[] JPF_ARGS = {INSN_FACTORY, SYM_METHOD};

  @Test
  public void mainTest() {
    if (verifyNoPropertyViolation(JPF_ARGS)) {
      TestPathCondition test = new TestPathCondition();

      test.test(11.0f, 21.0f, 31.0, 41.0, 51, 61);
    }
  }
}

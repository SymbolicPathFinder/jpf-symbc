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

public class TestInvokeSTATICandVIRTUAL extends InvokeTest{
	@Preconditions("x>0.0&&y>0.0")
	private static void testFloat(float x, float y) {
		if (x > y)
			System.out.println("br1");
		else
			System.out.println("br2");
	}

	@Preconditions("x>0.0&&y>0.0")
	private static void testDouble(double x, double y) {
		if (x > y)
			System.out.println("br1");
		else
			System.out.println("br2");
	}

	@Preconditions("x>0.0&&y>0.0")
	private void testDoubleThis(double x, double y) {
		if (x > y)
			System.out.println("br1");
		else
			System.out.println("br2");
	}
	private void testSimple(int i) {
		i++;
		System.out.println("here");
	}
	@Preconditions("x>0.0&&y>0.0")
	private void testFloatDoubleThis(float x, double y) {
		if (x > y)
			System.out.println("br1");
		else
			System.out.println("br2");
	}
	private static void test1(float x, float y) {
		System.out.println("test1");
		float z = x + y;
//		float z = 0.0f;
//		z = z / y;
		if (x > 1.1f) z = y;
		if (z > 30.0f) z = 91.0f;  // Array out of bounds exception
		z = x * z;
		z = -z;
//		z = z % 3.0f;
		z = z - y;
	}

	private static void test2(double x, double y) {
		double z = x + y;
//		double z = 0.0;
//		z = z / y;
		if (x > 1.1) z = y;  // BinaryRealExpression / IntegerExpression class cast exception
		if (z > 30.0) z = 91.0;  // BinaryRealExpression / IntegerExpression class cast exception
		z = x * z;
		z = -z;
//		z = z % 3;
		z = z - y;
	}
	void test3(float x, float y) {
		double z = x + y;
//		double z = 0.0;
//		z = z / y;
		if (x > 1.1) z = y;  // BinaryRealExpression / IntegerExpression class cast exception
		if (z > 30.0) z = 91.0;  // BinaryRealExpression / IntegerExpression class cast exception
		z = x * z;
		z = -z;
//		z = z % 3;
		z = z - y;
	}
	void test4(double x, double y) {
		double z = x + y;
//		double z = 0.0;
//		z = z / y;
		if(x!=y)
			System.out.println("x!=y");
		else
			System.out.println("x==y");
			/*
		if (x > 1.1) z = y;  // BinaryRealExpression / IntegerExpression class cast exception
		if (z > 30.0) z = 91.0;  // BinaryRealExpression / IntegerExpression class cast exception
		z = x * z;
		z = -z;
//		z = z % 3;
		z = z - y;
		*/
	}
	void test5(int x, int y) {

		if (x > y)
			System.out.println("***x>y");
		else
			System.out.println("***x<y");
	}
    static void test6(int x, int y) {

		if (x > y)
			System.out.println("***x>y");
		else
			System.out.println("***x<y");
	}
    static void test7(int x, double y, float z) {

		if (x > y)
			System.out.println("*** x>y");
		else
			System.out.println("*** x<y");
		if (y > z)
			System.out.println("*** y>z");
		else
			System.out.println("*** y<z");
	}
    void test8(double x, int y, double z) {

		if (x > y)
			System.out.println("*** x>y");
		else
			System.out.println("*** x<y");
		if (y > z)
			System.out.println("*** y>z");
		else
			System.out.println("*** y<z");
	}

  public static void main(String[] args) {
    runTestsOfThisClass(args);
	}

  private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.TestInvokeSTATICandVIRTUAL.testFloat(sym#sym)";
  private static final String[] JPF_ARGS = {INSN_FACTORY, SYM_METHOD};

  @Test
  public void mainTest() {
    if (verifyNoPropertyViolation(JPF_ARGS)) {
      double x = 7.0;
      double y = 9.0;
      testFloat((float)x,(float)y);
      testDouble(x,y);
      (new TestInvokeSTATICandVIRTUAL()).testDoubleThis(x,y);
      (new TestInvokeSTATICandVIRTUAL()).testFloatDoubleThis((float)x,y);
      //(new TestInvokeSTATICandVIRTUAL()).testSimple(0);
      //test1(11.0f, 21.0f);
      //test2(11.0, 21.0);
      //(new TestInvokeSTATICandVIRTUAL()).test3(0.0f, 0.0f);
      //(new TestInvokeSTATICandVIRTUAL()).test4(0.0, 0.0);
      //(new TestInvokeSTATICandVIRTUAL()).test5(0, 0);
      //test6(0, 0);
      //test7(0,0,0);
      //(new TestInvokeSTATICandVIRTUAL()).test8(0, 0,0);
    }
  }

}

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

public class ExSymExe30 {
	
	@Symbolic ("true")
	static float staticGlobalFloat = 0.1f;
	@Symbolic ("true")
	float globalFloat = 4.4f;
	@Symbolic ("true")
	static int staticGlobalInt = 0;
	@Symbolic ("true")
	int globalInt = 4;
	
  public static void main (String[] args) {
	  float x = 3;
	  float y = 5;
	  ExSymExe30 inst = new ExSymExe30();
	  inst.test(x, y, 9.99f);
  }

  /*
   * test FNEG, FADD, FSUB, FDIV, FMUL, FREM, FCMPG & FCMPL bytecodes
   */
  
  //public void test (float x, float z, float r) { //invokevirtual
  public static void test (float x, float z, float r) { //invokestatic
  //private void test (float x, float z, float r) { //invokespecial
	  
	  float a = staticGlobalFloat;
	  float b = z;
	  float c = 3.45f; 
	  float d = z - staticGlobalFloat;
	  
	  float negate = -r; //FNEG
	  
	  float sum = a + b; //FADD
	  float sum2 = z + 5.5f; //FADD
	  float sum3 = 5.5f + z; //FADD
	  
	  float diff = a - b; //FSUB
	  float diff2 = d - 1.0f; //FSUB
	  float diff3 = 2.3f - a; //FSUB
	  
	  float div = a / b; //FDIV
	  float div2 = 1.0f / a; //FDIV
	  float div3 = d / 2.2f; //FDIV
	  
	  float mul = a * b; //FMUL
	  float mul2 = a * 2.2f; //FMUL
	  float mul3 = 2.2f * d; //FMUL
	  
	  float remain = a % d; //FREM - not supported
	  	  
	  System.out.println("Testing ExSymExe30");
	  
	  if ( x < z) //FCMPG
	  //if ( mul2 <= mul) //FCMPG
	  //if ( mul2 != mul) //FCMPL
		  System.out.println("branch FOO1");
	  else
		  System.out.println("branch FOO2");
	  if (x > r)  //FCMPL
		  System.out.println("branch BOO1");
	  else
		  System.out.println("branch BOO2");
		  
  }
}
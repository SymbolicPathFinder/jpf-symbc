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

public class ExSymExeLongBCwGlob2 {
	
	@Symbolic("true")
	static long staticGlobalLong = 10909;
	@Symbolic("true")
	long globalLong = 898989;
	@Symbolic("true")
	static int staticGlobalInt = 0;
	@Symbolic("true")
	int globalInt = 4;
	
  public static void main (String[] args) {
	  long x = 3;
	  long y = 5;
	  ExSymExeLongBCwGlob2 inst = new ExSymExeLongBCwGlob2();
	  inst.test(x, y);
  }

  /*
   * test LADD, LCMP, LMUL, LNEG, LSUB, invokevirtual bytecodes
   * using globals
   */
  
  public void test (long x, long z) { //invokevirtual
	  
	  System.out.println("Testing ExSymExeLongBCwGlob2");
	  
	  long a = x;
	  long b = z;
	  long c = staticGlobalLong; 

	  long negate = -z; //LNEG
	  
	  long sum = a + b; //LADD
	  long sum2 = z + 9090909L; //LADD
	  long sum3 = c + globalLong; //LADD
	  
	  long diff = a - b; //LSUB
	  long diff2 = b - c; //LSUB
	  long diff3 = 9999999999L - a; //LSUB
	    	  
	  long mul = a * b; //LMUL
	  long mul2 = a * 19999999999L; //LMUL
	  long mul3 = c * b; //LMUL
	  
	  if ( globalLong > sum)
		  System.out.println("branch globalLong > sum");
	  else
		  System.out.println("branch globalLong <= sum");
	  if (x < z)
		  System.out.println("branch x < z");
	  else
		  System.out.println("branch x >= z");
		  
  }
}
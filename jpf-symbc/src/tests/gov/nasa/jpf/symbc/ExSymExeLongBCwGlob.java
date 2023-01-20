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

public class ExSymExeLongBCwGlob {
	
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
	  ExSymExeLongBCwGlob inst = new ExSymExeLongBCwGlob();
	  inst.test(x, y);
  }

  /*
   * test invokespeical, LCMP bytecode
   * using globals
   */
  
  private void test (long x, long z) { //invokespecial
	  
	  System.out.println("Testing ExSymExeLongBCwGlob");
	  
	  long a = x;
	  long b = z;
	  long c = staticGlobalLong; 

	  if ( globalLong > x)
		  System.out.println("branch globalLong > x");
	  else
		  System.out.println("branch globalLong <= x");
	  if (c < z)
		  System.out.println("branch c < z");
	  else
		  System.out.println("branch c >= z");
		  
  }
}
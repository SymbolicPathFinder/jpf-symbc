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

public class ExSymExeLongBytecodes2 {
	
  public static void main (String[] args) {
	  long x = 3;
	  long y = 5;
	  ExSymExeLongBytecodes2 inst = new ExSymExeLongBytecodes2();
	  inst.test(x, y);
  }

  /*
   * test LADD, LAND, LCMP, LOR, LREM, LSHL, LSHR, LSUM, LUSHR, LXOR bytecodes
   * no globals
   */
  
  public void test (long x, long z) { //invokevirtual
	  
	  System.out.println("Testing ExSymExeLongBytecodes2");
	  
	  long a = x;
	  long b = z;
	  long c = 34565; 
/*
	  long remain = a % c; //LREM - not supported
	  long res = 999999999999L & remain;  //LAND - not supported
	  long res2 = remain/c;  //LDIV - not supported
	  remain = remain | res2;  //LOR - not supported
	  remain = remain ^ res2; //LXOR - not supported
	  res = res << res2; //LSHL - not supported
	  res = res >> res2; //LSHR - not supported
	  res = res >>> res2; //LUSHR - not supported
	  long div = a / b; //LDIV - not supported  
*/	  
	  long sum = a + b; //LADD
	  
	  long temp = ( a < 0)? sum: b-a;
	  	 
	  if ( temp > c)
		  System.out.println("branch diff > c");
	  else
		  System.out.println("branch diff <= c");
		  
  }
}
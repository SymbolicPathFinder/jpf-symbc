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

import gov.nasa.jpf.symbc.Symbolic;

/*
 * test method with no parameters and two symbolic methods called
 */
public class ExSymExe32 {
	
	@Symbolic ("false")
	static int global;
	@Symbolic ("false")
	int global2;
	@Symbolic ("false")
	boolean glob;
	
  public static void main (String[] args) {
	  System.out.println("Testing ExSymExe32");
	  int x = 2;  
	  ExSymExe32 inst = new ExSymExe32();
	  global = 9;
	  inst.global2 = 0;
	  int y = global*x;
	  inst.test(y,9);
	  inst.test1();
  }
  
  public void test (int x, int z) {
	  int y = 3;
	  x = x + z ;
	  z = z + y;
	  if (z > 0)
		  System.out.println("branch FOO1");
	  else
		  System.out.println("branch FOO2");
	  if (x > 0)
		  System.out.println("branch BOO1");
	  else
		  System.out.println("branch BOO2");
  }

  public void test1(){
	  int y = 3;
	  y = y + 1;
	  global = y;
	  if (y > 3)
		  System.out.println("BAR1");
	  else
		  System.out.println("BAR2");
  }
}

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

public class ExSymExe8 {
	
  public static void main (String[] args) {
	  int x = 3;
	  int y = 5;
	  ExSymExe8 inst = new ExSymExe8();
	  inst.test(x,y);
  }

  /*
   * test ISUB & IFGE bytecodes (Note: javac compiles "<" to IFGE)
   */
  public void test (int x, int z) {
	  System.out.println("Testing ExSymExe8");
	  int y = 3;
	  int p = 2;
	  x = z - y ;
	  z = z - p;
	  if (z < 0)
		  System.out.println("branch FOO1");
	  else
		  System.out.println("branch FOO2");
	  if (x < 0)
		  System.out.println("branch BOO1");
	  else
		  System.out.println("branch BOO2");
  }
}


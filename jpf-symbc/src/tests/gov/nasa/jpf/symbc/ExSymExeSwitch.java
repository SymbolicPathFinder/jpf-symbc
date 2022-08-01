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


public class ExSymExeSwitch {

  public static void main (String[] args) {
	  int x = -1; /* we want to specify in an annotation that this param should be symbolic */


	  test(x);
  }
  /* we want to let the user specify that this method should be symbolic */

  public static void test (int x) {
	  x=x+1 ;

//	  switch (x) {
//	  case 0: System.out.println("branch Foo0"); break;
//	  case 1: System.out.println("branch Foo1"); break;
//	  default: System.out.println("default1"); break;
//	  }


	  switch (x) {
	  case 2: System.out.println("branch Foo2"); break;
	  case 3000: System.out.println("branch Foo3000"); break;
	  default: System.out.println("default2"); break;
	  }


  }

}


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

package gov.nasa.jpf.symbc.strings;

import gov.nasa.jpf.symbc.Debug;

public class ExSymExeStringsFailed {

	public static void main (String[] args) {
		  String a="aaa";
		  test (a);
		  Debug.printPC("This is the PC at the end:");
		  
	  }
	  
	  public static void test (String a) {
		  int i = 0;
		 
		  if(!a.contains("a")){ 
			  i++;
		  }
		  if (a.startsWith("a")) {
			  i++;
		  }
		  if (i == 2) {
			  throw new RuntimeException("");
		  }
	  }

}
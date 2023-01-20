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


public class ExSymExeStrings62 {
	static int field;

  public static void main (String[] args) {
	  String a = "ddd";
	  //test (a);
	  fixedtest("a");
	  Debug.printPC("This is the PC at the end:");
	  //a=a.concat(b);
	  
  }
  
  public static void test (String str){
	  str = str.replace ('a', 'b');
	  if (str.contains("a")) {
		  throw new RuntimeException ("Gats");
	  }
	    
  }
  
  public static void fixedtest (String str){
	  if (str.contains("a") && str.length() < 3) {
		 str = str.replace ('a', 'b');
		 for (int i = 0; i < str.length(); i++) {
			 if (str.charAt(i) == 'a') {
				 throw new RuntimeException ("Gats");
			 }
		 }
	  }
	    
  }
  
  public static void buggedtest (String str){
	  if (str.contains("a") && str.length() < 3) {
		 str.replace ('a', 'b');
		 for (int i = 0; i < str.length(); i++) {
			 if (str.charAt(i) == 'a') {
				 throw new RuntimeException ("Gats");
			 }
		 }
	  }
	    
  }

}


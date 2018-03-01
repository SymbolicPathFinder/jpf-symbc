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


public class ExSymExeStrings55 {
	static int field;

  public static void main (String[] args) {
	  String a="aaa";
	  String b = "bbb";
	  String c = "ccc";
	  String d = "ddd";
	  test ("aaa", 1);
	  //Debug.printPC("This is the PC at the end:");
	  //a=a.concat(b);
	  
  }
  
  public static void test (String a, int d) { 
	  System.out.println("start");
	  int i = 0;
	  int len = a.length();
	  char c = a.charAt(i);
	  if (c == '<') {
		  System.out.println("int: " + a);
		  if (i + 14 < len &&
					(a.charAt(i + 8) == '\"')
					&&
					(a.charAt(i + 7) == '=')
					&&
					(a.charAt(i + 6) == 'f' || a.charAt(i + 6) == 'F')
					&&
					(a.charAt(i + 5) == 'e' || a.charAt(i + 5) == 'E')
					&&
					(a.charAt(i + 4) == 'r' || a.charAt(i + 4) == 'R')
					&&
					(a.charAt(i + 3) == 'h' || a.charAt(i + 3) == 'H')
					&&
					(a.charAt(i + 2) == ' ')
					&&
					(a.charAt(i + 1) == 'a' || a.charAt(i + 1) == 'A')
					) {
			  
		  	int idx = 0 + 9;
			int x = a.indexOf("\"", idx);
			int y = a.indexOf('>', x);
			int z = a.indexOf("</a>", y);
			if (z == -1) {
				d = a.indexOf("</A>", y);
				if (d == -1) {
					throw new RuntimeException("aaa!");
				}
			}
			
			//i = idxEnd + 4;
		  }
	  }
	  System.out.println("end");
  }

}


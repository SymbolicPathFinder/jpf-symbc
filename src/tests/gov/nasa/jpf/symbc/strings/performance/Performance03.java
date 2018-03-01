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

package gov.nasa.jpf.symbc.strings.performance;

public class Performance03 {
	
	/*
	 * Path condition explosion.
	 * 
	 * There is one variable to play with here, "someNumber" in method "test", which sets the number of paths to be explored
	 * . The number of paths will be someNumber * 100.
	 */
	public static void main (String [] args) {
		test("a", "b", "c");
	}
	
	public static void test (String a, String b, String c) {
		int someNumber = 10;
		  if (a.length() < someNumber && b.length() < someNumber && c.length() < someNumber) {
			  for (int i = 0; i < someNumber; i++) {
				  if (a.charAt(i) == 'a') {
					  System.out.println("a");
				  }
				  else if (a.charAt(i) == 'b') {
					 
					  System.out.println("b");
				  }
				  else if (a.charAt(i) == 'c') {
					  /*if (a.equals("ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")) {
						  throw new RuntimeException("aah!");
					  }*/
					  System.out.println("c");
				  }
				  else if (a.charAt(i) == 'd') {
					  System.out.println("d");
				  }
				  else if (a.charAt(i) == 'e') {
					  System.out.println("e");
				  }
				  else if (a.charAt(i) == 'f') {
					  System.out.println("f");
				  }
				  else if (a.charAt(i) == 'g') {
					  System.out.println("g");
				  }
				  else if (a.charAt(i) == 'h') {
					  System.out.println("h");
				  }
				  else if (a.charAt(i) == 'i') {
					  System.out.println("i");
				  }
				  else if (a.charAt(i) == 'j') {
					  System.out.println("j");
				  }
				  else if (a.charAt(i) == 'k') {
					  System.out.println("k");
				  }
				  else if (a.charAt(i) == 'l') {
					  System.out.println("l");
				  }
				  else if (a.charAt(i) == 'm') {
					  System.out.println("m");
				  }
				  else if (a.charAt(i) == 'n') {
					  System.out.println("n");
				  }
				  else if (a.charAt(i) == 'o') {
					  System.out.println("o");
				  }
				  else if (a.charAt(i) == 'p') {
					  System.out.println("p");
				  }
				  else if (a.charAt(i) == 'q') {
					  System.out.println("q");
				  }
				  else if (a.charAt(i) == 'r') {
					  System.out.println("r");
				  }
				  else if (a.charAt(i) == 's') {
					  System.out.println("s");
				  }
				  else if (a.charAt(i) == 't') {
					  System.out.println("t");
				  }
				  else if (a.charAt(i) == 'u') {
					  System.out.println("u");
				  }
				  else if (a.charAt(i) == 'v') {
					  System.out.println("v");
				  }
				  else if (a.charAt(i) == 'w') {
					  System.out.println("w");
				  }
				  else if (a.charAt(i) == 'x') {
					  System.out.println("x");
				  }
				  else if (a.charAt(i) == 'y') {
					  System.out.println("y");
				  }
				  /*if (b.startsWith("d")) {
					  throw new RuntimeException("aaah!");
				  }*/
				  if (b.startsWith(a)) {
					  System.out.println("aah");
				  }
				  if (c.endsWith(a)) {
					  System.out.println("boo");
				  }
			  }
		  }
	}
}

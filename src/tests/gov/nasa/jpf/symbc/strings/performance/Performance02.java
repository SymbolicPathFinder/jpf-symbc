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

public class Performance02 {
	private static final int MAX_LENGTH = 5;
	
	/*
	 * string-integer constraint performance testing.
	 * 
	 * There is one dimension to set here, and that is choosing which testX method to run
	 */
	public static void main (String [] args) {
		//test ("ajzcb", 3,2,1);
		//test2 ("ajzcb", 3,2,1, 3,2,1);
		//test3 ("ajzcb", 3,2,1, 3,2,1, 3,2,1);
		test4 ("ajzcb", 3,2,1, 3,2,1, 3,2,1, 3,2,1);
	}
	
	public static void test (String a, int i1, int j1, int k1) {
		int count = 0;
		if (i1 > -1 && j1 > -1 && k1 > -1) {
			if (a.startsWith("a")) {
				System.out.println("Step 1");
				count++;
			}
			if (a.endsWith("b")) {
				System.out.println("Step 2");
				count++;
			}
			if (a.indexOf("c") == i1) {
				System.out.println("Step 3");
				count++;
			}
			/*if (a.lastIndexOf("z") == j1) {
				System.out.println("Step 4");
				count++;
			}*/
			if (a.charAt(k1) == 'j') {
				System.out.println("Step 5");
				count++;
			}
			/*if (count == 5) {
				throw new RuntimeException("look at this");
			}*/
		}
	}
	
	public static void test2 (String a, int i1, int i2, int j1, int j2, int k1, int k2) {
		int count = 0;
		if (i1 > -1 && j1 > -1 && k1 > -1 && i2 > -1 && j2 > -1 && k2 > -1) {
			if (a.startsWith("aa")) {
				System.out.println("Step 1");
				count++;
			}
			if (a.endsWith("bb")) {
				System.out.println("Step 2");
				count++;
			}
			if (a.indexOf("c") == i1) {
				System.out.println("Step 3");
				count++;
			}
			if (a.indexOf("d") == i2) {
				System.out.println("Step 4");
				count++;
			}
			/*if (a.lastIndexOf("y") == j1) {
				System.out.println("Step 5");
				count++;
			}
			if (a.lastIndexOf("z") == j2) {
				System.out.println("Step 6");
				count++;
			}*/
			if (a.charAt(k1) == 'j') {
				System.out.println("Step 7");
				count++;
			}
			if (a.charAt(k2) == 'k') {
				System.out.println("Step 8");
				count++;
			}
			/*if (count == 8) {
				throw new RuntimeException("look at this");
			}*/
		}
	}
	
	public static void test3 (String a, int i1, int j1, int k1, int i2, int j2, int k2, int i3, int j3, int k3) {
		int count = 0;
		if (i1 > -1 && j1 > -1 && k1 > -1 && i2 > -1 && j2 > -1 && k2 > -1 && i3 > -1 && j3 > -1 && k3 > -1) {
			if (a.startsWith("aaa")) {
				System.out.println("Step 1");
				count++;
			}
			if (a.endsWith("bbb")) {
				System.out.println("Step 2");
				count++;
			}
			if (a.indexOf("c") == i1) {
				System.out.println("Step 3");
				count++;
			}
			if (a.indexOf("d") == i2) {
				System.out.println("Step 4");
				count++;
			}
			if (a.indexOf("e") == i3) {
				System.out.println("Step 5");
				count++;
			}
			/*if (a.lastIndexOf("x") == j1) {
				System.out.println("Step 6");
				count++;
			}
			if (a.lastIndexOf("y") == j2) {
				System.out.println("Step 7");
				count++;
			}
			if (a.lastIndexOf("z") == j3) {
				System.out.println("Step 8");
				count++;
			}*/
			if (a.charAt(k1) == 'j') {
				System.out.println("Step 9");
				count++;
			}
			if (a.charAt(k2) == 'k') {
				System.out.println("Step 10");
				count++;
			}
			if (a.charAt(k3) == 'l') {
				System.out.println("Step 11");
				count++;
			}
			/*if (count == 11) {
				throw new RuntimeException("look at this");
			}*/
		}
	}
	
	public static void test4 (String a, int i1, int j1, int k1, int i2, int j2, int k2, int i3, int j3, int k3, int i4, int j4, int k4) {
		int count = 0;
		if (i1 > -1 && j1 > -1 && k1 > -1 && i2 > -1 && j2 > -1 && k2 > -1 && i3 > -1 && j3 > -1 && k3 > -1 && i4 > -1 && j4 > -1 && k4 > -1) {
			if (a.startsWith("aaaa")) {
				System.out.println("Step 1");
				count++;
			}
			if (a.endsWith("bbbb")) {
				System.out.println("Step 2");
				count++;
			}
			if (a.indexOf("c") == i1) {
				System.out.println("Step 3");
				count++;
			}
			if (a.indexOf("d") == i2) {
				System.out.println("Step 4");
				count++;
			}
			if (a.indexOf("e") == i3) {
				System.out.println("Step 5");
				count++;
			}
			if (a.indexOf("f") == i4) {
				System.out.println("Step 6");
				count++;
			}
			/*if (a.lastIndexOf("w") == j1) {
				System.out.println("Step 7");
				count++;
			}
			if (a.lastIndexOf("x") == j2) {
				System.out.println("Step 8");
				count++;
			}
			if (a.lastIndexOf("y") == j3) {
				System.out.println("Step 9");
				count++;
			}
			if (a.lastIndexOf("z") == j4) {
				System.out.println("Step 10");
				count++;
			}*/
			if (a.charAt(k1) == 'j') {
				System.out.println("Step 11");
				count++;
			}
			if (a.charAt(k2) == 'k') {
				System.out.println("Step 12");
				count++;
			}
			if (a.charAt(k3) == 'l') {
				System.out.println("Step 13");
				count++;
			}
			if (a.charAt(k4) == 'm') {
				System.out.println("Step 14");
				count++;
			}
			if (count == 14) {
				throw new RuntimeException("look at this");
			}
		}
	}
}

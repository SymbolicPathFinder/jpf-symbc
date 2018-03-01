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

package strings;

import java.util.Random;

//This example featured in the paper: "Precise Analysis of String Expressions". Can not be solved yet
public class Tricky {
	static String bar(int n, int k, String op) {
		if (k==0) return "";
		return op+n+"]"+bar(n-1,k-1,op)+" ";
	}

	static String foo(int n) {
		String b = "";
		if (n<2) b += "(";
		for (int i=0; i<n; i++) b += "(";
		String s = bar(n-1,n/2-1,"*").trim();
		String t = bar(n-n/2,n-(n/2-1),"+").trim();
		//String s = bar(n-1,n-1,"*").trim();
		//String t = bar(n-2,n-2,"+").trim();
		//return b.toString()+n+(s+t).replace(']',')');
		return b+n+(s+t);
	}

	public static void test (int n) {
		String s = foo (n);
		System.out.println(s);
	}

	public static void main(String args[]) {
		/*int n = new Random().nextInt();
		System.out.println(new Tricky().foo(n));*/
		test(5);
	}
}

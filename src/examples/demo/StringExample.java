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

package demo;

import gov.nasa.jpf.symbc.Debug;

public class StringExample {
	
	public static void main (String[] args) {
		System.out.println("start");
		test("<<<<<a href=\">    @");
		System.out.println ("end");
	}
	
	public static void test(String body) {
		if (body == null)
			return;
		int len = body.length();
		for(int i=0; i< len; i++) 
			if (body.charAt(i) != '<') 
				return;
		System.out.println("false "+Debug.getSymbolicStringValue(body));
		assert false;
	}
}
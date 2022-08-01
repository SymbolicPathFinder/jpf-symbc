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

import gov.nasa.jpf.symbc.Debug;



public class Assume {
	public int test(int x, int y) {
		Debug.assume(x>y);
		return x-y;
	}
	public int test1(int x, int y) {
		Debug.assume(x>y);
		return x-y;
	}
	
	// The test driver
	public static void main(String[] args) {
		Assume testinst = new Assume();
		int x = testinst.test(1, 2);
		 x = testinst.test1(1, 2);
		System.out.println("symbolic value of x: "+Debug.getSymbolicIntegerValue(x));
		Debug.printPC("\n Path Condition: ");
	}
}
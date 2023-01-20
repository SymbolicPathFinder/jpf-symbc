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

package summerschool;

import gov.nasa.jpf.symbc.Debug;

public class SwapSimple {

	static void test(int x, int y) {
		System.out.println("Initial values:");
		System.out.println("x: "+Debug.getSymbolicIntegerValue(x));
		System.out.println("y: "+Debug.getSymbolicIntegerValue(y));
		
		if (x > y) { 
			x = x + y; 
			y = x - y;
			x = x - y;
			
		}
		
		if (x >= y) 
			assert false;
		
		System.out.println("Final values:"+Debug.getSolvedPC());
		System.out.println("x: "+Debug.getSymbolicIntegerValue(x));
		System.out.println("y: "+Debug.getSymbolicIntegerValue(y));
		
		
	}
	public static void main(String[] args) {	
		test(0,0);
	}
}

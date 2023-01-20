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

package uberlazy;

/**
 * @author Neha Rungta
 *  A test driver for checking the values in the equivalence
 *  classes when variables of primitive type differ in their
 *  values. 
 *  **/


import gov.nasa.jpf.symbc.Symbolic;


public class TestPrimitiveFieldDiff {
	
	@Symbolic("true")
	Node n;
	@Symbolic("true")
	Node m;
	
	public void run() {
		if(m != null) {
			// when a primitive field reference is "used"	
			// and it differs in the value/type then the partition
			// function separates the ones that are different
			if(m.elem > 10) {
				if(n != null) {
					if(n.elem < 10) {
						System.out.println("m.elem is > 10 and n.elem < 10");
					}
				}
			} else {
				System.out.println("m.elem <= 10");
			}
		}
	}
	
	
	
	public static void main(String[] args) {
		TestPrimitiveFieldDiff tt = new TestPrimitiveFieldDiff();
		tt.run();
	}
	
}
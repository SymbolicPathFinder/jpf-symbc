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


public class TestParentFieldInit {
	
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
				System.out.println("the value of m.elem is greater 10");
				m.print();
			} else {
				System.out.println("less than equal to 10");
				m.print();
			}
			/**if(m.testElem > 10) {
				System.out.println("the value of Node.testElem is greater than 10++++++++++++++++++++++++++++++++++++++++");
				m.print();
				System.out.println("########################################");
			} else {
				System.out.println("the value is less than 10 -------------------------------------------");
				
			}**/
		}
	}
	
	public void testRun(Node x) {
		
		if(x != null) {
			if(x.elem > 10) {
				System.out.println("it is greater than 10");
				x.print();
			}
		}
	}
	
	public void differentField() {
		if(n != null) {
			// when a primitive field reference is read	
			// and it differs in the value then the partition
			// function separates the ones that are different 
			if(n.elem < 5) { 
				System.out.println("the value of n.elem is less 5");
			} 
		}
	}
	
	public static void main(String[] args) {
		TestParentFieldInit tt = new TestParentFieldInit();
		System.out.println("coming to the TestPrimTypeFieldDiff");
		tt.run();
		/**Node t0 = new Node();
		t0.elem = 12;
		intNode t1 = new intNode();
		t1.elem = 12;
		dblNode t2 = new dblNode();
		t2.elem = 12;
		tt.testRun(t0);
		tt.testRun(t1);
		tt.testRun(t2); **/
	}
	
}
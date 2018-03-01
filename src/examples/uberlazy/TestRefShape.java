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

import gov.nasa.jpf.symbc.Symbolic;

/**
 * @author Neha Rungta
 * This class tests building equivalence classes and the partition
 * function for differing shapes when a store operation occurs on
 * a data-structure of a non-primitive type. 
 **/


public class TestRefShape {
	@Symbolic("true")
	Node m;
	@Symbolic("true")
	Node n;
	
	public void run() {
		if(m != null) {
			System.out.println("m is not null");
			if(m.next != null) {
				System.out.println("one level nesting");
			}
			//@SuppressWarnings("unused")
			//Node tmp = m.next;
			//tmp = swapNode();
		}
	}
	
	public Node swapNode() {
		System.out.println("coming in swapNode");
		if(n != null) {
			System.out.println("\t n is not null");
			if(n.next !=null) {	
				System.out.println("\t \t n.next is not null");
				Node t = n.next;
				n.next = t.next;
				t.next = n;
				return t;
			}
		}
		return n;
	}
	
	public static void main(String[] args) {
		TestRefShape tt = new TestRefShape();
		tt.run();
	}
	
}
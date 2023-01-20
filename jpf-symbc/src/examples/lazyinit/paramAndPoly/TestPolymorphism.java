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

/**
 * @author Neha Rungta
 * @datecreated 01/26/10
 * @description: This example is take from "Efficient Symbolic
 * Execution Algorithms for Program Manipulating Dynamic Heap
 * Objects" By Xianghu Deng, Jooyong Lee, and Robby. The example
 * is used to demonstrate that the lazy initialization algorithm
 * handles the the "Liskov substitution principle" that states
 * a instance of a subtype can be used anywhere an object of a
 * supertype in the class heirarchy of the subtype is used. 
 * 
 * Node n1 and ExtendedNode en are symbolic objects. The pre-
 * condition to the isNext and isNextObject methods in Node
 * class is that the "this" object is not null. 
 * 
 * Additionally this example also tests lazy initialization of
 * objects that are passed as parameters to the methods. 
 * 
 */

package lazyinit.paramAndPoly;

public class TestPolymorphism {
	
	
	public boolean swapAndCheckNode(Node n) {
		if(n != null) {
			if (n.next != null) {
				Node t = n.next;
				n.next = t.next;
				t.next = n;
				return (t instanceof intNode);
			}
			return (n instanceof intNode);
		}
		return false;
	}
	
	public static void main( String [] args) {
		TestPolymorphism tp = new TestPolymorphism();
		Node n = null;
		boolean result = tp.swapAndCheckNode(n);
		System.out.println("the value of result is" + result);
	}
}
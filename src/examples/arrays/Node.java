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

package arrays;

public class Node {
	
	short elem;
	Node next;
	static int testElem;
	
	public Node () {
		
	}
	public boolean isNextObject (Object node) {
		return this.next == node;
	}
	
	public void print() { 
		System.out.println("I am a just a Node");
	}
	
	public void onePrint() {
		System.out.println("all types of nodes use this onePrint method");
	}
	
	public void testVal() {
		if(elem > 9) {
			System.out.println("the value is greater than 9");
		} else {
			System.out.println("the value is less than or equal to 9");
		}
	}
	
	public void testAll() {
		if(this.elem > 0) {
			System.out.println("the value is greater than 0");
		} else {
			System.out.println("the value is less than or equal to 0");
		}
	}
}

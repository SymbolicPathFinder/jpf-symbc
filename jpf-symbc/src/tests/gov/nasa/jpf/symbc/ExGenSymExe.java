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

package gov.nasa.jpf.symbc;


public class ExGenSymExe {

	public static void main (String[] args) {
		Node n = new Node();
		Node m = new Node();
		n.next = m;
		n.next.next=n;
		Node na = n.swapNode();
		//Debug.printSymbolicRef(n);
		//Debug.printPC("\nPC");
		//Debug.printHeapPC("Heap PC");
	}

	static class Node {
		int elem;
		Node next;
        static Node static_next;
		Node swapNode() {
			static_next = new Node();
			static_next.next = new Node();
			static_next.next.next = new Node();
			System.out.println("static_next "+static_next);
			System.out.println("static_next.next "+static_next.next);
			System.out.println("static_next.next.next "+static_next.next.next);
			if (next!=null)
				if(elem > next.elem) {
					Node t = next;
					next = t.next;
					t.next = this;
					return t;
				}
			return this;
		}
	}
}
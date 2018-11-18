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

public class Node {
	int elem;
	Node next;

	Node swapNode() {
		
		if(next!=null) 
			if(elem>next.elem) {
				Node t = next;
				next = t.next;
				t.next=this;
				assert elem < t.next.elem;
				return t;
			}
		return this;
	}
	
	public static void main(String[] args) {	
		Node n = new Node();
		n = (Node) Debug.makeSymbolicRef("node", n);
		if (n!=null) {
			Node result =n.swapNode();
			Debug.printPC("PC");
			Debug.printHeapPC("heap PC");
			Debug.printSymbolicRef(result, "result list");	
		}
	}
}

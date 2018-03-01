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

public class ExLazyList {


	public static void main(String[] args) {
		Node n = new Node();
		//n.swapNode();
		test(n);
		
	}

	public static void test(Node node){
		if(node!=null)
			node.swapNode();
	}
	
	public static class Node {

		@Symbolic("true")
		public int elem;
		
		@Symbolic("true")
		public Node next;

		public Node swapNode() {
			//System.out.println(Debug.getSymbolicIntegerValue(elem));
			Node result=this;
			System.out.println("start");
			if (next != null) {
				if (elem > next.elem) {
					Node t = next;
					next = t.next;
					t.next = this;
					result = t;
				}
			}
			Debug.printSymbolicRef(result, "node = ");
			return result;
		}
	}
}

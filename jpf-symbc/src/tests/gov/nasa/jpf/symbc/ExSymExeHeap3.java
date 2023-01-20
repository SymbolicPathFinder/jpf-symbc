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


public class ExSymExeHeap3 {

	static class Node  {
		int elem;
		Node next;
		static int static_field1;
		static int static_field2;


		  /* we want to let the user specify that this method should be symbolic */
		  Node swapNode() {

		 if (static_field1 > static_field2)
			  static_field1 = 0;
		 else
			  static_field2 = 1;


		  if(next!=null)
			  if(elem > next.elem) {
				  Node t = next;
				  next = t.next;
				  t.next = this;
				  return t;
			  }
		  return this;
		  }
	}


  public static void main (String[] args) {

	  Node n = new Node();
	  Debug.makeFieldsSymbolic("input_n", n);
	  Node m = n.swapNode();
	  Debug.printHeapPC("HeapPC: ");
	  Debug.printPC("PC: ");
	  Debug.printSymbolicRef(m,"return:");
	  System.out.println("*****************");
  }

}


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


public class ExSymExeHeap {

	static class Node  {
		//@Symbolic("true")
		int elem;

		//Symbolic("true")
		Node next;


		  /* we want to let the user specify that this method should be symbolic */
		  Node swapNode() {

		  if(next!=null)
			  if(elem > next.elem) {
				  elem = 0;
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
	  Node m = new Node();
	  //Debug.makeFieldsSymbolic("input_n", n);
	  n =  (Node) Debug.makeSymbolicRef("input_n", n);
	  //Debug.makeFieldsSymbolic("input_m", m);
	  if (n !=null)
		  m = n.swapNode();
	  Debug.printHeapPC("HeapPC: ");
	  Debug.printPC("PC: ");
	  Debug.printSymbolicRef(m,"return:");
	  System.out.println("*****************");
  }

}


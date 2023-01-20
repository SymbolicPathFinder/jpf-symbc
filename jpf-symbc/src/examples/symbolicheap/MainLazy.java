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

package symbolicheap;

/**
 * @author pcorina
 *
 */

public class MainLazy {
	
	//	from TACAS'03 paper "Generalized Symbolic Execution ..."
	static Node swapNode (Node l) {
		if (l.next != null)
			if (l.elem > l.next.elem) {
				Node t = l.next;
		        l.next = t.next;
		        t.next = l;
		        return t;
			}
		return l;
	}
	
	
	
	public static void main(String[] args) {
		Node l = Node._get_Node();
		
		if(l!=null) {
			Node t = l.swapNodeSymbolic();
		}
		System.out.println(">>>>");
		Node.printOriginalListCycles(l);
	}
}


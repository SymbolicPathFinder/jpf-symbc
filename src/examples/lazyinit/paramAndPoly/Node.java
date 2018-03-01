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

package lazyinit.paramAndPoly;


public class Node {

	Node next;
	
	public boolean isNext(ExtendedNode node) {
		return this.next == node;
		
	}
	
	public boolean isNextObject(Object node) {
		if( this.next == node )
			return true;
		else  {
			nextObjectTypeHierarchy(node);
			return false;
		}
	}
	
	void nextObjectTypeHierarchy(Object node) {
		if(!(node instanceof Node)) {
			if(this.next != node) {
				System.out.println("this.next != node");
			} else{
				System.out.println("===equal====: assert failed");
			}
		}
	}
	
}
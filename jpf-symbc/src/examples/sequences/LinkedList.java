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

package sequences;



class LinkedListNode{
	public int data;
	public LinkedListNode next;
	public LinkedListNode(int x){
		data = x;
		next = null;
	}
}

/**
 *
 * @author Mithun Acharya
 *
 */
public class LinkedList {
	private LinkedListNode head;
	private LinkedListNode tail;

	public LinkedList(){
		head = null;
		tail = null;
	}

	boolean insertFront(int x){
		LinkedListNode newNode = null;
		newNode = new LinkedListNode(x);
		if (newNode == null){
			return false;
		}
		newNode.next = head;
		head = newNode;
		return true;
	}

	boolean find(int x){
		LinkedListNode current = head;
		while(current!=null && current.data != x)
			current = current.next;
		if (current == null) return false;
		return true;
	}

	boolean deleteElement(LinkedListNode deleteMe){
		LinkedListNode current = head;

		if (head == deleteMe){
			head = head.next;
			return true;
		}

		while(current!=null){
			if (current.next == deleteMe){
				current.next = deleteMe.next;
				return true;
			}
			current = current.next;
		}
		return false;
	}
}

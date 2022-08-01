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



class BSTNode {
	public int value;

	public BSTNode left, right;

	public BSTNode(int x) {
		value = x;
		left = null;
		right = null;
	}

}

/**
 * Taken from issta2006.BinTree
 *
 */
public class BinTree {

	private BSTNode root;

	public BinTree() {
		root = null;
	}


	public void add(int x) {
		BSTNode current = root;

		if (root == null) {
			root = new BSTNode(x);
			return;
		}

		while (current.value != x) {
			if (x < current.value) {
				if (current.left == null) {
					current.left = new BSTNode(x);
				} else {
					current = current.left;
				}
			} else {
				if (current.right == null) {
					current.right = new BSTNode(x);
				} else {
					current = current.right;
				}
			}
		}
	}

	public boolean find(int x) {
		BSTNode current = root;

		while (current != null) {

			if (current.value == x) {
				return true;
			}

			if (x < current.value) {
				current = current.left;
			} else {
				current = current.right;
			}
		}

		return false;
	}

	public boolean remove(int x) {
		BSTNode current = root;
		BSTNode parent = null;
		boolean branch = true; //true =left, false =right

		while (current != null) {

			if (current.value == x) {
				BSTNode bigson = current;
				while (bigson.left != null || bigson.right != null) {
					parent = bigson;
					if (bigson.right != null) {
						bigson = bigson.right;
						branch = false;
					} else {
						bigson = bigson.left;
						branch = true;
					}
				}

				//		System.out.println("Remove: current "+current.value+" parent "+parent.value+" bigson "+bigson.value);
				if (parent != null) {
					if (branch) {
						parent.left = null;
					} else {
						parent.right = null;
					}
				}

				if (bigson != current) {
					current.value = bigson.value;
				} else {;
				}

				return true;
			}

			parent = current;
			//	    if (current.value <x ) { // THERE WAS ERROR
			if (current.value > x) {
				current = current.left;
				branch = true;
			} else {
				current = current.right;
				branch = false;
			}
		}

		return false;
	}

}

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

import gov.nasa.jpf.vm.Verify;
import gov.nasa.jpf.symbc.Debug;

import java.util.HashSet;
import java.util.Set;

/**
 * @author pcorina
 *
 */

// this is the original lazy approach
class Node {
	int elem;
	Node next;
	boolean _symbolic_next = true; // attribute
	int hashcode = 0;
	
	Node original_next; //used to keep original structure (not sure if we'll need it any more

	static java.util.Vector _v = new java.util.Vector();
	static {
		_v.add(null);
	}

//	public Node() {
//		_symbolic_next = true;
//		hashcode = this.hashCode();
//		elem = Debug.makeSymbolicInteger("SYM_elem_"+hashcode);
//	}


	public static Node _get_Node() { // takes care of aliasing
		int i = Verify.random(_v.size());
		if (i < _v.size())
			return (Node) _v.elementAt(i);
		Node t = Node._new_Node();
		_v.add(t);
		return t;
	}
	

	static Node _new_Node() {
		Node t = new Node();
		t._symbolic_next = true;
		t.hashcode = t.hashCode();
		t.elem = Debug.makeSymbolicInteger("SYM_elem_"+t.hashcode);
		return t;
	}

	public void _set_next(Node _value) {
		next =  _value;
		_symbolic_next = false;
	}

	public Node _get_next() {
		if (_symbolic_next) {
			_symbolic_next = false;
			next = Node._get_Node();
			original_next = next;
		}
		return next;
	}
	
	static void printOriginalList(Node head) {
		for (Node t = head; t != null; t = t.original_next) {
			System.out.println(
				"node"
				+ t.hashcode
				+ " elem = "
				+ (Debug.getSymbolicIntegerValue(t.elem))
				+ " next = "	
					+ ((t._symbolic_next) ? "*" : 
					   ((t.original_next != null) ? "node" 
					    + t.original_next.hashcode : "null")));
		}
	}

        static void printOriginalListCycles(Node head) {
	    Set visited = new HashSet();
		for (Node t = head; t != null; t = t.original_next) {
		    if(visited.add(t)) {
			System.out.println(
				"node"
				+ t.hashcode
				+ " elem = "
				+ (Debug.getSymbolicIntegerValue(t.elem))
				+ " next = "	
					+ ((t._symbolic_next) ? "*" : 
					   ((t.original_next != null) ? "node" 
					    + t.original_next.hashcode : "null")));
		    }
		    else
			return;
		}
	}
        static String printOriginalListCyclesString(Node head) {
	    String result = " ";
	    Set visited = new HashSet();
		for (Node t = head; t != null; t = t.original_next) {
		    if(visited.add(t)) {
			result = result +
				"node"
				+ t.hashcode
				+ " elem = "
				+ (Debug.getSymbolicIntegerValue(t.elem))
				+ " next = "	
					+ ((t._symbolic_next) ? "*" : 
					   ((t.original_next != null) ? "node" 
					    + t.original_next.hashcode : "null")) +"\n";
		    }
		    else
			return result;
		}
		return result;
	}

	static String printOriginalNode(Node t) {
		if (t == null)
			return "null";	
		return "node" + t.hashcode
		+ " elem = "	+ (Debug.getSymbolicIntegerValue(t.elem))
		+ " next = "	+ ((t._symbolic_next) ? "*" : ((t.original_next != null) ? "node" 
							       + t.original_next.hashcode : "null"));
	}

	Node swapNodeSymbolic () {
		if (_get_next() != null)
			if (elem > _get_next().elem) {
				Node t = _get_next();
		        _set_next(t._get_next());
		        t._set_next(this);
		        return t;
			}
		return this;
	}


}
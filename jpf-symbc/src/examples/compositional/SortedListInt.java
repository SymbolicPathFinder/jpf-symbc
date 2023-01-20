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

package compositional;

class SLNode {
	int data;
	SLNode next;

	public SLNode(int data, SLNode next) {
		this.data = data;
		this.next = next;
	}

	public SLNode(int data) {
		this.data = data;
	}

	public SLNode() {
	}

	public boolean equals(Object obj) {
		if (obj instanceof SLNode) {
			SLNode node;
			node = (SLNode) obj;
			if (node.next == null)
				return this.next == null && this.data == node.data;
			if (this.next == null)
				return node.next == null && this.data == node.data;
			return this.data == (node.data) && this.next.equals(node.next);
		}
		return false;
	}

	// Example borrowed from \cite{DBLP:conf/tacas/KhurshidPV03}
	public SLNode swapNode() {
		if (next != null)
			if (data > next.data) {
				SLNode t = next;
				next = t.next;
				t.next = this;
				return t;
			}
		return this;
	}

}// class SLNode

public class SortedListInt {
	//Fields
	SLNode first;

	//Methods

	public SortedListInt(){
		first = null;
	}//Constructor

	public boolean empty(){
		return (first == null);
	}

	public void insert(int data){
		SLNode curr, foll;

		if ((first == null) || (data <= first.data)) // Insertion at the beginning
			first = new SLNode(data,first);
		else {
			curr = first; foll = first.next;
			while ((foll != null) && (foll.data < data)){
				curr = foll; foll = foll.next;
			}
			curr.next = new SLNode(data,foll);
		}
	}//insert

	public void reverse(SortedListInt l){
	    SLNode curr, foll, prev;
	    prev = null;
	    curr = l.first;
	    while (curr != null) {	
		foll = curr.next;
		curr.next = prev;
		prev = curr;
		curr = foll;
	    }
	    l.first = prev;
	}//reverse

	public void insertAll(int[] dataArr){
		for (int i = 0;i < dataArr.length;i++)
			insert(dataArr[i]);
	}

	public void merge(SortedListInt l){
		SLNode p1,p2,prev;

		p1 = first; p2 = l.first;
		if (p1.data <= p2.data) 
		    p1 = p1.next;
		else { first = p2; p2 = p2.next; }

		prev = first;
		while ((p1 != null) && (p2 != null)){
			if (p1.data <= p2.data){
				prev.next = p1;
				p1 = p1.next;
			} 
			else {
				prev.next = p2;
				p2 = p2.next;
			}
			prev = prev.next;
		}

		if (p1 == null) 
		    prev.next = p2;
		else prev.next = p1;
	}

    //if (first == null) first = l.first;
    //else if (!l.empty()) { // this and l are not empty


    public void mergeAll(SortedListInt[] ls){
	for (int i = 0; i< ls.length; i++)
	    merge(ls[i]);
    }

	public String toString(){
		String out = "[";
		SLNode aux = first;
		while (aux != null){
			out += aux.data;
			aux = aux.next;
			if (aux != null)
				out += ",";
		}//while
		out += "]";
		return out;
	}
	public boolean equals(Object obj){
                if (obj instanceof SortedListInt){
                	SortedListInt  list;
                	list= (SortedListInt) obj;
                	if (list.first==null) return this.first==null;
                	if (this.first==null) return list.first==null;
                	return this.first.equals(list.first);
             	}
        	return false;
        }

	public static void main(String[] args) {
		SortedListInt l1 = new SortedListInt();
		int[] d1 = {3,3};
		l1.insertAll(d1);
		System.out.println(l1);

		SortedListInt l2 = new SortedListInt();
		int[] d2 = {2,4};
		l2.insertAll(d2);
		System.out.println(l2);
		l1.merge(l2);
		System.out.println(l1);
		SortedListInt l3 = new SortedListInt();
		int[] d3 = {1,2,3,4};
		l3.insertAll(d3);		
		l3.reverse(l3);
		System.out.println(l3);

	}

}

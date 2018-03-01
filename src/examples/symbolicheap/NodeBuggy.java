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

import gov.nasa.jpf.symbc.Debug;

public class NodeBuggy {

	int elem;
    NodeBuggy next;
    NodeBuggy left;
    NodeBuggy right;
	
    public NodeBuggy(int x) {
    	elem = x;
    	next = null;
    	left = null;
    	right = null;
    }
	
    void addGCIssue() {

       // this.left = (NodeBuggy) Debug.makeSymbolicRef("tmp", new NodeBuggy(5));
        Debug.printSymbolicRef(left, "left = ");
        this.left = null;

        if (this.right != null) {

        
        Debug.printSymbolicRef(right, "right = ");
        System.out.println(this.right.left);
        }

}


	void addSimple3() {
		int depth = 0;
    	NodeBuggy bigson = this;
    	while (bigson.left != null || bigson.right != null) {
    		if (bigson.right != null) {
    			bigson = bigson.right;			
    		} else {
    			bigson = bigson.left;
    		}
    		depth++;
    		if (depth == 2)
    			return;
		}
	}

	void addSimple3b() {
		int depth = 2;
    	NodeBuggy bigson = this;
    	while (((bigson.left != null || bigson.right != null)) && depth > 0) {
    		if (bigson.right != null) {
    			bigson = bigson.right;			
    		} else {
    			bigson = bigson.left;
    		}
    		depth--;
		}
	}
	static void addSimple(NodeBuggy n) {
		if(n==null) return;
		int depth = 2;
    	NodeBuggy bigson = n;
    	while (((bigson.left != null || bigson.right != null)) && depth > 0) {
    		if (bigson.right != null) {
    			bigson = bigson.right;			
    		} else {
    			bigson = bigson.left;
    		}
    		depth--;
		}
	}
	
	
	void addSimple4() {
    	NodeBuggy bigson = this;
    	if (bigson.left != null || bigson.right != null) {
    		if (bigson.right != null) {
    			bigson = bigson.right;			
    		} else {
    			bigson = bigson.left;
    		}
		}
    	if (bigson.left != null || bigson.right != null) {
    		if (bigson.right != null) {
    			bigson = bigson.right;			
    		} else {
    			bigson = bigson.left;
    		}
		}
	}
	
	public static void runTest(int x) {
    	NodeBuggy X = new NodeBuggy(5);
        X = (NodeBuggy) Debug.makeSymbolicRef("input_X", X);
        if (X != null) {
            X.addSimple3b();//broken
            //X.addSimple4(); //working
        }
        //Debug.printSymbolicRef(X, "node = ");
    }
	
	public static void main(String[] args) {	
		//addSimple(null);
		//runTest(1);
		NodeBuggy X = new NodeBuggy(5);
        X = (NodeBuggy) Debug.makeSymbolicRef("input_X", X);
		if(X!=null) X.addGCIssue();
	}

}

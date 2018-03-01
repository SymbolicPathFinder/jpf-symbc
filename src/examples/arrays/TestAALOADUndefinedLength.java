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

package arrays;


public class TestAALOADUndefinedLength {
	
	public void run(Node[] nlist) {
        Node test = nlist[10];
        for (int i = 0; i<nlist.length; i++) {
            Node n = nlist[i];
    		if(n != null) {
                int curr = 100/n.elem;
		    	
	    	} else {
		    	System.out.println("n is null");
	    	}
        }
	}
	
	
	public static void main(String[] args) {
		TestAALOADUndefinedLength taaload = new TestAALOADUndefinedLength();
		Node[] n = {new Node()}; 
		taaload.run(n);
	}
}

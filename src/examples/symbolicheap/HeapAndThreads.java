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
 * from test for missed paths in concurrent threads with very little interaction
 * in core
 */

class HeapAndThreads {
	
	  static class X {
	    boolean pass;
	   X next;
	  }
      static X readX(X someX) { return someX;}
      static X readXsimple(boolean somePass) { 
    	  X someX=new X(); 
    	  someX.pass=somePass;
    	  return someX;
    	  }
	  static class InstanceFieldPropagation extends Thread {
	    X myX; // initially not set

	    public void run() {
	     // myX = readXsimple(true);	
	     myX = readX(null); 
	     if (myX!=null && myX.next!=null && myX.pass){
	        System.out.println("T: accessed global myX");
	        if (!myX.pass){  // (2) won't fail unless main is between (0) and (1)
	          throw new AssertionError("gotcha");
	        }
	      }
	    }    
	  }

	  
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		    
		      InstanceFieldPropagation mp = new InstanceFieldPropagation();
		      mp.start();
		      
		      X x = new X();
		      System.out.println("M: new " + x);
		      mp.myX = x;        // (0) x not shared until this GOT executed
		     
		      //Thread.yield();  // this would expose the error
		      System.out.println("M: x.pass=true");
		      x.pass = true;     // (1) need to break BEFORE assignment or no error
		    }
		 
	}


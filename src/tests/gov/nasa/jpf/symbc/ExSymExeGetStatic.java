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

public class ExSymExeGetStatic {
  
        public static void main (String[] args) {
            SNode sn = new SNode();
            SNode sn2 = sn.swap();
        }     
}
	       
class SNode{
	int elem;
	SNode next;
	static SNode head; //= new SNode(); //change is here
	
	SNode swap(){
		  if (head != null)
			  System.out.println("head is not null");
		  else
			  System.out.println("head is null");
		  return this;
	}
}



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


import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.Preconditions;

class StackNode {
  public int value;
  public StackNode next;

  public StackNode(int x) {
    value = x;
    next = null;
	}
}

/**
 *
 * @author Mithun Acharya
 *
 */
public class Stack {
  private StackNode top;

  public Stack( ) {
    top = null;
  }

  public boolean isEmpty( ) {
    return top == null;
  }

  @Preconditions("i>0")
  public void push(int i) {
    StackNode newStackNode = new StackNode(i);
    if (i == 0) System.out.println("pushed " + 0);
    else System.out.println("pushed " + "!0");
    newStackNode.next = top;
    top = newStackNode;
  }

  @Preconditions("dummy>0")
  public int pop(int dummy) {
    if(isEmpty( ))
    	throw new RuntimeException("empty stack");
    else{
    	int value = top.value;
    	top = top.next;
    	System.out.println("popping ");
    	return value;
    }
  }
}




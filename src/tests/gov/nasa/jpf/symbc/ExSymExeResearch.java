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

public class ExSymExeResearch {
  
  
  public static void main (String[] args) {
      int x = 3;
      int y = 5;
      ExSymExeResearch inst = new ExSymExeResearch();
      inst.test(x, y);
  }

 
  public int test (int a, int b) { //invokevirtual
	  int result=0;
      System.out.println("Testing ExSymExeResearch");
    if (a >=0 && a <100 && b>=0 && b <100) {
      int sum = a + b;
      int diff = a - b;
      int temp;
      
      if (sum > 0)
          temp = a;
      else
          temp = b;
      if (temp < diff)
          result = temp;
      else
          result = diff;
    }
    return result;
        
  }
}


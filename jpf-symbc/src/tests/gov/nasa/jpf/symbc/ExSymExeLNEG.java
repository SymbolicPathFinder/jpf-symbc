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

public class ExSymExeLNEG {
	
  public static void main (String[] args) {
	  long x = 3876543455L;
	  ExSymExeLNEG inst = new ExSymExeLNEG();
	  inst.test(x);
  }

  
  public void test (long x) {
	  System.out.println("Testing LNEG");
	  long y = - x;
	  if (y > 0)
		  System.out.println("branch -x > 0");
	  else
		  System.out.println("branch -x <= 0");
  }
}


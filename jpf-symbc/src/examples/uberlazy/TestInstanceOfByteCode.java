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

package uberlazy;

/**
 * @author Neha Rungta
 * 
 * This class tests whether all the non-deterministic choices arising
 * from polymorphism are accounted for. The initialization of the 
 * data structure n is all the classes that Node is an instanceof
 * It also serves as a test case when for the partition function 
 * at the non-deterministic choice of the instanceof class
 * 
 * Without the polymorphism only the second print statement will 
 * be executed. With polymorphism the first statements prints twice
 * and the else prints once. With the correct partition function
 * each statement prints once. 
 **/

import gov.nasa.jpf.symbc.Symbolic;


public class TestInstanceOfByteCode {
	
	@Symbolic("true")
	Node n;

	
	public void run () {
		if(n != null) {
			if(n instanceof dblNode) {
				System.out.println("You can store reals in this data structure");
			} else {
				System.out.println("Don't store a Real in here");
			}
		}
	}
	
	public static void main(String[] args) {
		TestInstanceOfByteCode tt = new TestInstanceOfByteCode();
		tt.run();
	}
	
}
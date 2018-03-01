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
 * Check for the partitioning of equivalence classes
 * when the instanceof operator is invoked 
 */

import gov.nasa.jpf.symbc.Symbolic;


public class TestInstanceOfOne{

	@Symbolic("true")
	Node n;

	public void run() {
		if(n != null ) {
			System.out.println("it is not null");
			if(n instanceof intNode) {
				System.out.println("it is an instance of intNode");
			} else if (n instanceof Node) {
				System.out.println("it is an instance of Node class ********************************");
			}
		}
	}
	
	public static void main (String[] args) {
		TestInstanceOfOne tt = new TestInstanceOfOne();
		tt.run();
	}
	
}
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

import gov.nasa.jpf.symbc.Symbolic;

public class TestRefCompareNeq {
	
	@Symbolic("true")
	Node n;
	@Symbolic("true")
	Node m;
	
	public void run () {
		if(n != null) {
			if(m != null) {
			//   the bytecode sequences that the following code is
			//	 15:	getfield	#2; //Field n:Luberlazy/Node;
			//   18:	aload_0
			//   19:	getfield	#3; //Field m:Luberlazy/Node;
			//   22:	if_acmpne	36

			// hence this example really is comparing inequality

				if(n == m) {
					System.out.println("the objects are equal");
				} else {
					System.out.println("They are not equal");
				}
			}
		}
	}

	
	public static void main (String[] args) {
		TestRefCompareNeq test = new TestRefCompareNeq();
		test.run();
	}
	
}
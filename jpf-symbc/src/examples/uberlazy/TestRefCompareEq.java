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

public class TestRefCompareEq {
	
	@Symbolic("true")
	Node n;
	@Symbolic("true")
	Node m;
	
	public void run () {
		if(n != null) {
			if(m != null) {
			//   the bytecode sequences that the following code is
				//   5:		getfield	#3; //Field m:Luberlazy/Node;
			  	//   8:		if_acmpeq	22
				//   11:	getstatic	#5; //Field java/lang/System.out:Ljava/io/PrintStream;
				//   14:	ldc	#6; //String the objects are equal
				// hence this example really is comparing equality

				if(n != m) {
					System.out.println("the objects are not equal");
				} else {
					System.out.println("They are equal");
				}
			}
		}
	}
	
	public void testEquality() {
		//   the bytecode sequences that the following code is
		//   5:		getfield	#3; //Field m:Luberlazy/Node;
	  	//   8:		if_acmpeq	22
		//   11:	getstatic	#5; //Field java/lang/System.out:Ljava/io/PrintStream;
		//   14:	ldc	#6; //String the objects are equal
		// hence this example really is comparing equality

		if(n != m) {
			System.out.println("the objects are not equal");
		} else {
			System.out.println("They are equal");
		}
	}
	
	
	public static void main (String[] args) {
		TestRefCompareEq test = new TestRefCompareEq();
		test.run();
	}
	
}
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

public class TestGeneral{
	
	@Symbolic("true")
	Node n;
	
	public void test(int val, int concVal) {
		if(n != null && n instanceof intNode) {
			intNode in = (intNode) n;
			if(in.elem == val) {
				System.out.println("Reached target");
			}
		}
	}
	
	public static void main(String[] args) {
		TestGeneral tg = new TestGeneral();
		int val = 0; // input
		int otherVal = 1;
		tg.test(val, otherVal);
	}
}
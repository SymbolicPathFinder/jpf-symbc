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

package concolic;

import gov.nasa.jpf.symbc.Concrete;

public class TestConcreteAnote {

	public static void runSymbolic(int x, double y) {
		if(x > 10) {
			//int y = runConcrete(x);
			if(y == runConcrete(y)) {
				//System.out.println("y is zero");
			}
			System.out.println("x > 10");
		} else {
			System.out.println("x <= 10");
		}
	}
	
	@Concrete("true")
	public static double runConcrete(double z) {
		System.out.println("running concrete");
		return 0.0;
	}
	
	public static void main(String[] args) {
		runSymbolic(1,0);
	}
}
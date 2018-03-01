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
import gov.nasa.jpf.symbc.Partition;

public class PartitionEx {
	
	public static void runSymbolic(double y) {
			if(y > runConcrete(y)) {
				System.out.println("greater than the input ");
			} else {
				System.out.println("less than the input");
			}
			System.out.println("x > 10");
	}
	
	@Concrete("true")
	@Partition({"z>5.0&&z<10.0","z>0.0"})
	public static double runConcrete(double z) {
		if(z == 10) {
			return z / 1.2;
		}
		return z * 1.2;
	}
	
	public static void main(String[] args) {
		PartitionEx.runSymbolic(10.0);
	}
}
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

public class TestStatCalc {
	
	public void run(int val) {
		
		System.out.println("adding value");
		StatCalculator.addValue(val);
		StatCalculator.addValue(val);
		StatCalculator.addValue(val);
		StatCalculator.addValue(val);
		//stat.addValue(val);
		if(StatCalculator.getMedian().intValue() == 3) {
			System.out.println("median value is 3");
		} else {
			System.out.println("median value is not 3");
		}
		if(StatCalculator.getStandardDeviation() <= 0.82915619758885) {
			System.out.println("std deviation is .10");
		} else {
			System.out.println("std deviation not found");
		}
	}
	
	public static void main(String[] args) {
		TestStatCalc stat = new TestStatCalc();
		stat.run(4);
		
	}
	
}
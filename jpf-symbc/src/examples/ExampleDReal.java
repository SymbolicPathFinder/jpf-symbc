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


public class ExampleDReal {
	
	public static void main(String[] args) {
		(new ExampleDReal()).test(0.0,0.0);
	}

	// this is a simplified example showing method abort taken from CEV_15EOR_LOR
    public void test (double in1, double in2) {
    	if(Math.sin(in1)>Math.abs(in2))
    		System.out.println("success");
    }
    
    
}

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


public class ImplicitFlow {
	
	int func(int H){
		int O;
		if (H == 0) O = 0;
		else if (H == 1) O = 1;
		else if (H == 2) O = 2;
		else if (H == 3) O = 3;
		else if (H == 4) O = 4;
		else if (H == 5) O = 5;
		else if (H == 6) O = 6;
		else O = 0;
		return O;
	}
	
	public static void main(String[] args) {
		ImplicitFlow imflow = new ImplicitFlow();
		System.out.println("Output is: " + imflow.func(1));
	}
	
}
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

package compositional;

public class DART_SMART {
// from P Godefroid
	
	int is_positive(int x) {
		if(x>0) return 1;
		return 0;
	}
	
	static int N = 100;
	void top(int [] s) {// N inputs
		int cnt = 0;
		for (int i=0; i< 100; i++)
			cnt=cnt+is_positive(s[i]);
		if(cnt==3)
			assert(false); //error
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		int[] in = new int[N];
		(new DART_SMART()).top(in);

	}
}

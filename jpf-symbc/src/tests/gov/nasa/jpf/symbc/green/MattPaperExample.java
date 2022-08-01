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

package gov.nasa.jpf.symbc.green;

//import gov.nasa.jpf.symbc.probsym.Analyze;

public class MattPaperExample {

	public static void covered(int br) {
	  // Analyze.coverage(""+br);
	}

	public static int m(int x, int y) {
		if (x < 0) x = -x;
		if (y < 0) y = -y;
		if (x < 10) return 1;
		else if (9 < y) return -1;
		else return 0;
	}

	public static void main(String[] args) {
		covered(10 + m(1, 1));
	}

}

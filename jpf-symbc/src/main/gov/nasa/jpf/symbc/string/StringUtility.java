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

package gov.nasa.jpf.symbc.string;

public class StringUtility {
	public static String findLeftSide (String entireString, String rightString) {
		
		int i = 1;
		while (i < rightString.length()) {
			if (entireString.charAt(entireString.length() - i) != rightString.charAt(rightString.length() - i)) {
				break;
			}
			i ++;
		}
		int index = entireString.length() - i;
		return entireString.substring(0, index);
	}
	
	public static String findRightSide (String entireString, String leftString) {
		
		int i = 0;
		while (i < leftString.length()) {
			if (entireString.charAt(i) != leftString.charAt(i)) {
				break;
			}
			i ++;
		}
		int index = i;
		return entireString.substring(index);
	}
}

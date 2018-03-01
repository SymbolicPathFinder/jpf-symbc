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

package strings;

public class MysteryQuestionMin {
	
	public static void main (String[] args) {
		System.out.println("start");
		preserveSomeHtmlTagsAndRemoveWhitespaces("<<<<<a href=\">    @");
		System.out.println ("end");
	}
	
	public static String preserveSomeHtmlTagsAndRemoveWhitespaces(String body) {
		if (body == null)
			return body;
		int len = body.length();
		int i = 0;
		int old = i - 1;
		while (i < len) {
			//assert i >= old: "Infinite loop";
			if (i < old) {
				throw new RuntimeException("Infinite loop");
			}
			old = i;
			if (body.charAt(i) == '<') {
				if (i + 14 < len &&
				(body.charAt(i + 8) == '\"')
				&&
				(body.charAt(i + 7) == '=')
				&&
				(body.charAt(i + 6) == 'f' || body.charAt(i + 6) == 'F')
				&&
				(body.charAt(i + 5) == 'e' || body.charAt(i + 5) == 'E')
				&&
				(body.charAt(i + 4) == 'r' || body.charAt(i + 4) == 'R')
				&&
				(body.charAt(i + 3) == 'h' || body.charAt(i + 3) == 'H')
				&&
				(body.charAt(i + 2) == ' ')
				&&
				(body.charAt(i + 1) == 'a' || body.charAt(i + 1) == 'A')
				) {
					int idx = i + 9;
					int idx2 = body.indexOf("\"", idx);
					int idxStart = body.indexOf('>', idx2);
					int idxEnd = body.indexOf("</a>", idxStart);
					if (idxEnd == -1)
						idxEnd = body.indexOf("</A>", idxStart);
					i = idxEnd + 4;
					continue;
				}
			}
			i++;
			

		}
		return "";
	}
}
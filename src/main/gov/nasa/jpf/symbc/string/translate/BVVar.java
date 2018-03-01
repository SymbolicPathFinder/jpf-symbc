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

package gov.nasa.jpf.symbc.string.translate;

import java.util.HashMap;
import java.util.Map;

public class BVVar implements BVExpr{
	String name;
	int size;
	
	public static Map<String, Integer> map;
	static Map<Integer, String> reverseMap;
	static int startInteger;
	
	public BVVar(String name, int size) {
		this.name = name;
		this.size = size;
	}
	
	public String toString () {
		return name;
	}
	
	public String toSMTLibDec () {
		
		int currentInteger;
		if (map == null) {
			map = new HashMap<String, Integer>();
			reverseMap = new HashMap<Integer, String>();
			startInteger = 1;
			currentInteger = 1;
			map.put(name, startInteger);
			reverseMap.put(startInteger, name);
			startInteger++;
		}
		else if (map.get(name) != null) {
			currentInteger = map.get(name);
		}
		else {
			map.put(name, startInteger);
			reverseMap.put(startInteger, name);
			currentInteger = startInteger;
			startInteger++;
		}
		//println ("map: " + map);
		StringBuilder sb = new StringBuilder();
		
		sb.append ("(declare-fun fun"); 
		sb.append (currentInteger);		
		sb.append (" () (_ BitVec ");
		sb.append (size);
		sb.append ("))");
		
		return sb.toString();
	}
	
	public static void println (String msg) {
		System.out.println("[BVVar]" + msg);
	}
	
	public String toSMTLib () {
		return "fun" + String.valueOf(map.get(name));
	}
}

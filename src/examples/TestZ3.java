
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

import gov.nasa.jpf.symbc.Debug;

public class TestZ3 {
	public static void testSimple(int x, int y) {
		if (x - y <= y)
			printResult("x - y <= y: " + Debug.getSolvedPC());
		else
			printResult("x - y  > y: " + Debug.getSolvedPC());
	}

	public static void testBitwiseOr(int x, int y) {
		if ((x | y) == 37) {
			printResult("x | y was 37");
		} else {
			printResult("x | y was 37");
		}

		if (37 == (x | y)) {
			printResult("x | y was 37");
		} else {
			printResult("x | y was 37");
		}

		if ((x | 31) == 31) {
			printResult("x | 31 was 31");
		} else {
			printResult("x | 31 was not 31");
		}

		if (31 == (x | 31)) {
			printResult("x | 31 was 31");
		} else {
			printResult("x | 31 was not 31");
		}
	}
	
	public static void testBitwiseAnd(int x, int y) {
		if ((x & y) == 37) {
			printResult("x & y was 37");
		} else {
			printResult("x & y was not 37");
		}

//		if (37 == (x & y)) {
//			printResult("x & y was 37");
//		} else {
//			printResult("x & y was not 37");
//		}
//
//		if ((x & 31) == 31) {
//			printResult("x & 31 was 31");
//		} else {
//			printResult("x & 31 was not 31");
//		}
//
//		if (31 == (x & 31)) {
//			printResult("x & 31 was 31");
//		} else {
//			printResult("x & 31 was not 31");
//		}		
	}
	
	public static void testShiftLeft(int x, int y) {
		if (x << 2 == 4) {
			printResult("x << 2 == 4");
		} else {
			printResult("x << 2 != 4");
		}
		
		if (2 << y == 4) {
			printResult("2 << y == 4");
		} else {
			printResult("2 << y != 4");
		}
		
		if (x << y == 4) {
			printResult("x << y == 4");
		} else {
			printResult("x << y != 4");
		}
	}
	
	public static void testShiftRight(int x, int y) {
		if (x >> 2 == 4) {
			printResult("x >> 2 == 4");
		} else {
			printResult("x >> 2 != 4");
		}
		
		if (8 >> y == 4) {
			printResult("8 >> y == 4");
		} else {
			printResult("8 >> y != 4");
		}
		
		if (x >> y == 4) {
			printResult("x >> y == 4");
		} else {
			printResult("x >> y != 4");
		}
	}
	
	public static void testLogicalShiftRight(int x, int y) {
		if (x >>> 2 == 4) {
			printResult("x >>> 2 == 4");
		} else {
			printResult("x >>> 2 != 4");
		}
		
		if (8 >>> y == 4) {
			printResult("8 >>> y == 4");
		} else {
			printResult("8 >>> y != 4");
		}
		
		if (x >>> y == 4) {
			printResult("x >>> y == 4");
		} else {
			printResult("x >>> y != 4");
		}
	}
	
	public static void testCombination(int x, int y) {
			if ((x >> y) == 1) {
				printResult("x >> y was 1");
				
				if (x + y == 4) {
					printResult("x >> y == 1 and x + y == 4");
				} else {
					printResult("NOT x >> y == 1 and x + y == 4");
				}
			}
	}
	
	public static void testBitwiseXor(int x, int y) {
		if ((x ^ y) == 37) {
			printResult("x ^ y was 37");
		} else {
			printResult("x ^ y was not 37");
		}

		if (37 == (x ^ y)) {
			printResult("x ^ y was 37");
		} else {
			printResult("x ^ y was not 37");
		}

		if ((x ^ 31) == 31) {
			printResult("x ^ 31 was 31");
		} else {
			printResult("x ^ 31 was not 31");
		}

		if (31 == (x ^ 31)) {
			printResult("x ^ 31 was 31");
		} else {
			printResult("x ^ 31 was not 31");		
		}
	}
	
	public static void testBitwiseCombination(int x, int y) {
		if ((x ^ y) == 3) {
			printResult("x ^ y was 3");
		} 
		
		if ((x | y) == 15) {
			printResult("x | y was 15");
		}
		
		if ((x + y) == 27) {
			printResult("x | y was 15");
		}
	}

	public static void testMod(int x, int y) {
		if (x % y == 23) {
			printResult("x % y was 23");
		} else {
			printResult("x % y was not 23");
		}
	}
	
	public static void printResult(String str) {
		System.out.println(str + (ISDEBUG ? ": " + Debug.getSolvedPC() : "."));
	}
	
	private static boolean ISDEBUG = true;

	public static void main(String[] args) {
		testMod(0, 0);
//		testSimple(0, 0);
//		testBitwiseXor(0, 0);
//		testBitwiseOr(0, 0);
//		testBitwiseAnd(0, 0);
//		testShiftLeft(0, 0);
//		testShiftRight(0, 0);
//		testLogicalShiftRight(0, 0);
//		testCombination(0, 0);
//		testBitwiseCombination(0, 0);
	}
}

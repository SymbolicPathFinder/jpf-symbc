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

/**
 * 
 */
package gov.nasa.jpf.symbc;

import org.junit.Test;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TestLCMPConditions extends InvokeTest {

	  private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.TestLCMPConditions.twoConditions(sym);gov.nasa.jpf.symbc.TestLCMPConditions.twoConditions2(sym)";
	  private static final String DEBUG = "+symbolic.debug=true";	  
	  private static final String DP = "+symbolic.dp=coral";	 
	  private static final String[] JPF_ARGS = {INSN_FACTORY, SYM_METHOD, DEBUG, DP};

	  public static void main(String[] args) {
	    runTestsOfThisClass(args);
	  }

	  @Test
	  public void mainTest() {
	    if (verifyNoPropertyViolation(JPF_ARGS)) {
	    	//twoConditions(20000000000L);
	    	twoConditions2(20000000L);
	    	//threeConditions(20000000000L, 20000000000L);
	    }
	  }
	  
	  public static void twoConditions(long a) {
		 if(a >= 50L) {
			 if(a >= 51L) {
				 long c = a + 2;
			 }
		 }
	  }
	  
	  public static void twoConditions2(long a) {
			 if(a <= 51L) {
				 if(a <= 50L) {
					 long c = a + 2;
				 }
			 }
		  }
	  
	  public static long threeConditions(long a, long b) {
		  long c = 10L;
		  if(a > b) {
			  c = 500L;
		  }
		  else if(b > a) {
			  c = 7000L;
		  }
		  else if(b == a) {
			  c = 1000L;
		  }
		  return c;		  
	  }
}

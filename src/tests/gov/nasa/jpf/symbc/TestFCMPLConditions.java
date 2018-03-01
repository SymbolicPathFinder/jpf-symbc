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
public class TestFCMPLConditions extends InvokeTest {

	  private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.TestFCMPLConditions.twoConditions(sym#sym);gov.nasa.jpf.symbc.TestFloatConditions.threeConditions(sym#sym)";
	  private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.SymbolicListener";
	  private static final String DEBUG = "+symbolic.debug=true";	  
	  private static final String DP = "+symbolic.dp=coral";
	  private static final String MININT = "+symbolic.minint=0";
	  
	  private static final String[] JPF_ARGS = {INSN_FACTORY, SYM_METHOD, LISTENER, DEBUG, DP, MININT};

	  public static void main(String[] args) {
	    runTestsOfThisClass(args);
	  }

	  @Test
	  public void mainTest() {
	    if (verifyNoPropertyViolation(JPF_ARGS)) {
	    	twoConditions(20.0f, 20.0f);
	    	//threeConditions(20.0f, 20.0f);
	    }
	  }
	  
	  public static float twoConditions(float a, float b) {
		  if(a >= 0.0f) {
			  return b;
		  }
		  return a;		  
	  }
	  
	  public static float threeConditions(float a, float b) {
		  float c = 10.0f;
		  if(a > b) {
			  c = 50.0f;
		  }
		  else if(b > a) {
			  c = 700.0f;
		  }
		  else if(b == a) {
			  c = 100.0f;
		  }
		  return c;		  
	  }
}

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

package coverage;

import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.symbc.numeric.PathCondition;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class JPF_coverage_CheckCoverage {
	private static Set<String> paths = new HashSet<String>();
	private static int caseNum = 0;

	public static void processTestCase(MJIEnv env, int objRef, int pathRef) {
		String path = env.getStringObject(pathRef);
    	if (! paths.contains(path)) {
    		paths.add(path);
    		Map<String,Object> varsVals = getPcVarsVals(env);
    		int x = (Integer)varsVals.get("x");
    		int y = (Integer)varsVals.get("y");
    		int origZ = new MyClassOriginal().myMethod(x, y);
    		int annoZ = new MyClassWithPathAnnotations().myMethod(x, y);
    		
    		caseNum++;
    		if (origZ == annoZ) {
    			System.out.format("TestCase %s:  x = %s  y = %s\nPath: %s\n\n",
    					caseNum, x, y, path);
    		} else {
    			System.out.format("Error for TestCase %s:  x = %s  y = %s\nPath: %s\n\n",
    					caseNum, x, y, path);
    			System.out.format("The annotated and original code got different results.\n" +
    					"Annotated Result: %s\n" +
    					"Original Result: %s\n\n",
    					annoZ, origZ);
    		}
    		
    	} else {
    		System.out.println("Already saw '" + path + "'");
    	}
    }
    
    private static Map<String,Object> getPcVarsVals(MJIEnv env) {
		Map<String,Object> varsVals = new HashMap<String,Object>();
		PathCondition pc = PathCondition.getPC(env);
		
		if (pc != null) {
			pc.solve();
			pc.header.getVarVals(varsVals);
		}
		return varsVals;
	}
}

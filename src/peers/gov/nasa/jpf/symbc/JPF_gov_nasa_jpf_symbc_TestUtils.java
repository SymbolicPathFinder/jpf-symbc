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

package gov.nasa.jpf.symbc;

import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;
import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.symbc.numeric.PathCondition;

public class JPF_gov_nasa_jpf_symbc_TestUtils extends NativePeer {
	@MJI
	public static int getPathCondition____Ljava_lang_String_2(MJIEnv env, int objRef) {
		PathCondition pc = PathCondition.getPC(env);
		if (pc != null) {
			return env.newString(pc.stringPC());
		}
		return env.newString("");
	}
	@MJI
	public static int getSolvedPathCondition____Ljava_lang_String_2(MJIEnv env, int objRef) {
		PathCondition pc = PathCondition.getPC(env);
		if (pc != null) {
			pc.solve();
			return env.newString(pc.toString());
		}
		return env.newString("");
	}
}

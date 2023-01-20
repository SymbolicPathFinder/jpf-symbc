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

import gov.nasa.jpf.ListenerAdapter;
import gov.nasa.jpf.search.Search;
import za.ac.sun.cs.green.util.Reporter;

public class GreenListener extends ListenerAdapter {

	public GreenListener() { }

	@Override
	public void searchFinished(Search s) {
		SymbolicInstructionFactory.greenSolver.shutdown();
		SymbolicInstructionFactory.greenSolver.report(new Reporter() {
			@Override
			public void report(String context, String message) {
				System.out.println(context + ":: " + message);
			}
		});

	}

}
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


import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.vm.ChoiceGenerator;

public class HeuristicListener extends PropertyListenerAdapter  {

	
	public HeuristicListener(Config conf, JPF jpf) {
	}


	public void stateAdvanced(Search search) {
		System.out.println("State advanced here.");
		ChoiceGenerator<?> cg = search.getVM().getSystemState().getChoiceGenerator();
		int n = cg.getTotalNumberOfChoices();
		if (cg instanceof PCChoiceGenerator) {
			System.out.println("got a PC choice generator "+ n + " "+
			((PCChoiceGenerator) cg).getNextChoice() + " "+((PCChoiceGenerator) cg).getCurrentPC());
		
		if(((PCChoiceGenerator) cg).getNextChoice()==0) { // replace this condition with yours
			System.out.println("backtrack");
			search.getVM().getSystemState().setIgnored(true);
		}
		
		}
	}
	
}

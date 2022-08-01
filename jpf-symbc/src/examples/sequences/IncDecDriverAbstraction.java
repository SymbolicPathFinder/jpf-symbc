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

package sequences;


import gov.nasa.jpf.vm.Verify;
import gov.nasa.jpf.symbc.Debug;


/**
 *
 * @author Mithun Acharya
 *
 * launch configuration
 * +vm.insn_factory.class=gov.nasa.jpf.symbc.SymbolicInstructionFactory
 * +vm.classpath=.
 * +vm.storage.class=
 * +search.multiple_errors=true
 * +symbolic.method=inc(sym);dec(sym)
 * +jpf.report.console.finished=
 * +jpf.listener=gov.nasa.jpf.symbc.abstraction.SymbolicAbstractionListener
 * IncDecDriverAbstraction
 *
 *
 */
public class IncDecDriverAbstraction {

	private static void testDriver(int length){
		IncDec incDec = new IncDec();
		System.out.println("before loop");
		for (int i =0; i < length; i++){
			Verify.beginAtomic();
			switch(Verify.random(1)){
		  		case 0:
		  			//System.out.println("i" + i + "case0");
		  			incDec.inc(1);
		  			break;
		  		case 1:
		  			//System.out.println("i" + i + "case1");
		  			incDec.dec(1);
		  			break;
			}
			Verify.endAtomic();
		}
	}

	public static void main(String[] args) {
		testDriver(2);
		Debug.printPC("Path Condition: ");
		System.out.println();
	}
}

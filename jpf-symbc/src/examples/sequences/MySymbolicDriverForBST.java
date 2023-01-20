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


import gov.nasa.jpf.symbc.Debug;

/**
 *
 * @author Mithun Acharya
 *
 */
public class MySymbolicDriverForBST {
	/*
	To run this driver, you need to configure your JPF command line arguments as
  	+vm.insn_factory.class=gov.nasa.jpf.symbc.SymbolicInstructionFactory
  	+vm.classpath=.
  	+vm.storage.class=
  	+symbolic.method=methodSequenceDriver(sym#sym)
  	+jpf.report.console.finished=
  	+jpf.listener=gov.nasa.jpf.symbc.SymbolicListener
  	MySymbolicDriverForBST
	*/
	public static void main(String[] args){
		MethodSequenceGeneratorTao methodSequenceGeneratorTao = new MethodSequenceGeneratorTao();
		// <className, number_of_public_methods, sequence_length, range>
		methodSequenceGeneratorTao.invokeMethodSequenceDriver("BST", 3, 3, 3);
		Debug.printPC("\nMySymbolicDriverForStack.testDriver Path Condition: ");
	}

}

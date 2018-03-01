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
package gov.nasa.jpf.symbc.bytecode;

import gov.nasa.jpf.jvm.bytecode.JVMInstructionVisitor;


/**
 * Access jump table by key match and jump
 * ..., key => ...
 */
public class LOOKUPSWITCH extends SwitchInstruction implements gov.nasa.jpf.vm.bytecode.LookupSwitchInstruction {

	public LOOKUPSWITCH (int defaultTarget, int numberOfTargets) {
	    super(defaultTarget, numberOfTargets);
	  }

	  public void setTarget (int index, int match, int target){
	    targets[index] = target;
	    matches[index] = match;
	  }


	  public int getLength() {
	    return 10 + 2*(matches.length); // <2do> NOT RIGHT: padding!!
	  }

	  public int getByteCode () {
	    return 0xAB;
	  }

	  public void accept(JVMInstructionVisitor insVisitor) {
		  insVisitor.visit(this);
	  }

}

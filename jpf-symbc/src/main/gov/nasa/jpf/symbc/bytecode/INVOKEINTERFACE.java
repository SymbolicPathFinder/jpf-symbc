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

import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;

// need to fix names



public class INVOKEINTERFACE extends gov.nasa.jpf.jvm.bytecode.INVOKEINTERFACE{
	public INVOKEINTERFACE(String clsName, String methodName, String methodSignature) {
	    super(clsName, methodName, methodSignature);
	  }
	@Override
	public Instruction execute(ThreadInfo th) {
		 int objRef = th.getCalleeThis(getArgSize());

		    if (objRef == -1) {
		      lastObj = -1;
		      return th.createAndThrowException("java.lang.NullPointerException", "Calling '" + mname + "' on null object");
		    }

		    MethodInfo mi = getInvokedMethod(th, objRef);

		    if (mi == null) {
		      String clsName = th.getClassInfo(objRef).getName();
		      return th.createAndThrowException("java.lang.NoSuchMethodError", clsName + '.' + mname);
		    }
		BytecodeUtils.InstructionOrSuper nextInstr = BytecodeUtils.execute(this, th);
        if (nextInstr.callSuper) {
            return super.execute(th);
        } else {
            return nextInstr.inst;
        }
    }
}

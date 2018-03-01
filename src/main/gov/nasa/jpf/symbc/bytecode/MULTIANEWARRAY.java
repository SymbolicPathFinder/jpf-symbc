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


import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.string.SymbolicLengthInteger;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ClassLoaderInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * Symbolic version of the MULTIANEWARRAY class from jpf-core. Like NEWARRAY,
 * the difference from the jpf-core version is a snippet to detect if a symbolic
 * variable is being used as the size of the new array, and treat it accordingly.
 * 
 * And someone should review this one too :)
 * TODO: to review
 */

public class MULTIANEWARRAY extends gov.nasa.jpf.jvm.bytecode.MULTIANEWARRAY {

	public MULTIANEWARRAY(String typeName, int dimensions) {
		super(typeName, dimensions);
	}

	@Override
	public Instruction execute(ThreadInfo ti) {
		arrayLengths = new int[dimensions];
		StackFrame sf = ti.getModifiableTopFrame();
		for (int i = dimensions - 1; i >= 0; i--) {
			Object attr = sf.getOperandAttr();
			
			if(attr instanceof SymbolicLengthInteger) {
				long l = ((SymbolicLengthInteger) attr).solution;
				assert(l>=0 && l<=Integer.MAX_VALUE) : "Array length must be positive integer";
				arrayLengths[i] = (int) l;
				sf.pop();
			} else 	if(attr instanceof IntegerExpression) {
				throw new RuntimeException("MULTIANEWARRAY: symbolic array length");
			} else {
				arrayLengths[i] = sf.pop();
			}
		}

		//the remainder of the code is identical to the parent class
		
		// there is no clinit for array classes, but we still have  to create a class object
		// since its a builtin class, we also don't have to bother with NoClassDefFoundErrors
		ClassInfo ci = ClassLoaderInfo.getCurrentResolvedClassInfo(type);
		if (!ci.isRegistered()) {
			ci.registerClass(ti);
			ci.setInitialized();
		}
		    
		int arrayRef = allocateArray(ti.getHeap(), type, arrayLengths, ti, 0);

		// put the result (the array reference) on the stack
		sf.push(arrayRef, true);

		return getNext(ti);
	}
}

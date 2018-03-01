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


import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

public class ISHR extends gov.nasa.jpf.jvm.bytecode.ISHR {

	@Override
	public Instruction execute (ThreadInfo th) {
		StackFrame sf = th.getModifiableTopFrame();
		IntegerExpression sym_v1 = (IntegerExpression) sf.getOperandAttr(0); 
		IntegerExpression sym_v2 = (IntegerExpression) sf.getOperandAttr(1);
		
	    int v1 = sf.pop();
	    int v2 = sf.pop();

	    sf.push(v2 >> v1, false);
	    
		if (! (sym_v1==null && sym_v2==null) ) {
			
			IntegerExpression result = null;
			if (sym_v1 != null) {
				if (sym_v2!=null) {
					//result = sym_v1._shiftR(sym_v2);
					// FIX: it's the second argument right shifted by the first argument
					result = sym_v2._shiftR(sym_v1);
				}
				else {// v2 is concrete
					//result = sym_v1._shiftR(v2);
					result = (new IntegerConstant((int) v2))._shiftR(sym_v1);
				}
			}
			else if (sym_v2 != null) {
				result = sym_v2._shiftR(v1);
			}

			sf.setOperandAttr(result);
		}
		return getNext(th);
	}
}

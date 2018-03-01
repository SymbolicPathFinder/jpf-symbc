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



import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

public class IINC extends gov.nasa.jpf.jvm.bytecode.IINC {
	public IINC(int localVarIndex, int incConstant){
		super(localVarIndex, incConstant);
	}
  @Override
  public Instruction execute (ThreadInfo th) {

    StackFrame sf = th.getModifiableTopFrame();

    IntegerExpression sym_v = (IntegerExpression) sf.getLocalAttr(index);
    Instruction next_insn = super.execute(th);
    if (sym_v != null) {
    	sf.setLocalAttr(index,sym_v._plus(increment));
    	//System.out.println("IINC "+sf.getLocalAttr(index));
    }
    return next_insn;
  }
}

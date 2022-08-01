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
package gov.nasa.jpf.symbc.bytecode.optimization;


import gov.nasa.jpf.symbc.bytecode.optimization.util.IFInstrSymbHelper;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;

public class DCMPL extends gov.nasa.jpf.jvm.bytecode.DCMPL {
	@Override
	public Instruction execute(ThreadInfo th) {
		StackFrame sf = th.getModifiableTopFrame();

		RealExpression sym_v1 = (RealExpression) sf.getOperandAttr(1);
		RealExpression sym_v2 = (RealExpression) sf.getOperandAttr(3);

		if (sym_v1 == null && sym_v2 == null) { // both conditions are concrete
			return super.execute(th);
		} else { // at least one condition is symbolic
			Instruction nxtInstr = IFInstrSymbHelper.getNextInstructionAndSetPCChoiceDouble(th, 
																					  this, 
																					  sym_v1,
																					  sym_v2,
																					  Comparator.LT, 
																					  Comparator.EQ,
																					  Comparator.GT);

			return nxtInstr;
		}
	}
}

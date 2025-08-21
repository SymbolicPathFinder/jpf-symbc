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

//Copyright (C) 2007 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.

//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.

//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.

package gov.nasa.jpf.symbc.bytecode;


import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.string.StringComparator;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

// we should factor out some of the code and put it in a parent class for all "if statements"
// TODO: to review: approximation

public class IFNONNULL extends gov.nasa.jpf.jvm.bytecode.IFNONNULL {
	public IFNONNULL (int targetPc) {
		super(targetPc);
	}

	@Override
	public Instruction execute(ThreadInfo ti) {
		StackFrame sf = ti.getModifiableTopFrame();
		Expression sym_v = (Expression) sf.getOperandAttr();

        Config conf = ti.getVM().getConfig();
        String[] npe = conf.getStringArray("nullPointer.exception");
        final boolean npe_flag = npe != null && npe[0].equalsIgnoreCase("true");

		if (sym_v == null) { // Concrete execution
			return super.execute(ti);
		} else { // Symbolic Execution
			if(npe_flag) {
                if (sym_v instanceof StringExpression) {
                    ChoiceGenerator<?> cg;

                    if (!ti.isFirstStepInsn()) { // This is what really returns results
                        cg = new PCChoiceGenerator(2);
                        ti.getVM().getSystemState().setNextChoiceGenerator(cg);
                        return this;
                    } else {
                        cg = ti.getVM().getSystemState().getChoiceGenerator();
                        assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;

                        PathCondition pc;
                        ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();

                        while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
                            prev_cg = prev_cg.getPreviousChoiceGenerator();
                        }

                        if (prev_cg == null) {
                            pc = new PathCondition();
                        } else {
                            pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();
                        }

                        assert pc != null;

                        sf.pop(); // remove the operand from the stack

                        boolean currentChoice = (Integer) cg.getNextChoice() == 0;

                        // two choices (EQUALS, "null") | (NOTEQUALS, "null")
                        if (currentChoice) {
                            pc.spc._addDet(StringComparator.EQUALS, (StringExpression) sym_v, "null");
                            if (!pc.simplify()) {
                                ti.getVM().getSystemState().setIgnored(true);
                            } else {
                                ((PCChoiceGenerator) cg).setCurrentPC(pc);
                            }
                            return getNext(ti);
                        } else {
                            pc.spc._addDet(StringComparator.NOTEQUALS, (StringExpression) sym_v, "null");
                            if (!pc.simplify()) {
                                ti.getVM().getSystemState().setIgnored(true);
                            } else {
                                ((PCChoiceGenerator) cg).setCurrentPC(pc);
                            }
                            return getTarget();
                        }
                    }
                } else {
                    return ti.createAndThrowException("java.lang.UnsupportedOperationException", "IFNONNULL for non-string symbolic expressions is not supported.");
                }
            } else {
                sf.pop();
                return getTarget();
            }
		}
	}
}
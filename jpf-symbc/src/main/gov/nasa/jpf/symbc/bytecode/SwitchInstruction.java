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

//
//Copyright (C) 2007 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.
//
//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.
//
//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

package gov.nasa.jpf.symbc.bytecode;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * common root class for LOOKUPSWITCH and TABLESWITCH insns
 * 
 * YN: fixed choice selection in symcrete support (Yannic Noller <nolleryc@gmail.com>)
 */

public abstract class SwitchInstruction extends gov.nasa.jpf.jvm.bytecode.SwitchInstruction {
    protected SwitchInstruction(int defaultTarget, int numberOfTargets) {
        super(defaultTarget, numberOfTargets);
    }

    @SuppressWarnings("deprecation")
    @Override
    public Instruction execute(ThreadInfo ti) {
        StackFrame sf = ti.getModifiableTopFrame();
        IntegerExpression sym_v = (IntegerExpression) sf.getOperandAttr();

        if (sym_v == null) { // the condition is concrete
            return super.execute(ti);
        } else { // the condition is symbolic
            ChoiceGenerator<?> cg;

            if (!ti.isFirstStepInsn()) { // first time around
                cg = new PCChoiceGenerator(SymbolicInstructionFactory.collect_constraints ? 1 : matches.length + 1);
                ((PCChoiceGenerator) cg).setOffset(this.position);
                ((PCChoiceGenerator) cg).setMethodName(this.getMethodInfo().getCompleteName());
                ti.getVM().getSystemState().setNextChoiceGenerator(cg);
                return this;
            } else { // this is what really returns results
                cg = ti.getVM().getSystemState().getChoiceGenerator();
                assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
            }
            int value = sf.pop();
            PathCondition pc;
            // pc is updated with the pc stored in the choice generator above
            // get the path condition from the
            // previous choice generator of the same type

            // TODO: could be optimized to not do this for each choice
            ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);

            if (prev_cg == null)
                pc = new PathCondition();
            else
                pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();

            assert pc != null;
            int idx;
            if (SymbolicInstructionFactory.collect_constraints) {
                // Find which concrete branch corresponds the the value. If none, then idx == matches.length, which
                // means that the default branch is chosen.
                for (idx = 0; idx < matches.length; idx++) {
                    if (value == matches[idx]) {
                        break;
                    }
                }
                ((PCChoiceGenerator) cg).select(idx); // YN: set the choice correctly
            } else {
                idx = (Integer) cg.getNextChoice();
            }
            if (idx == matches.length) { // default branch
                lastIdx = DEFAULT;
                for (int i = 0; i < matches.length; i++)
                    pc._addDet(Comparator.NE, sym_v, matches[i]);
                if (!pc.simplify()) {// not satisfiable
                    ti.getVM().getSystemState().setIgnored(true);
                } else {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                }
                return mi.getInstructionAt(target);
            } else {
                lastIdx = idx;
                pc._addDet(Comparator.EQ, sym_v, matches[idx]);
                if (!pc.simplify()) {// not satisfiable
                    ti.getVM().getSystemState().setIgnored(true);
                } else {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                }
                return mi.getInstructionAt(targets[idx]);
            }
        }
    }

}

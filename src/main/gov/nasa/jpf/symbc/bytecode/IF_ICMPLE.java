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

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

//we should factor out some of the code and put it in a parent class for all "if statements"

/**
 * YN: fixed choice selection in symcrete support (Yannic Noller <nolleryc@gmail.com>)
 */
public class IF_ICMPLE extends gov.nasa.jpf.jvm.bytecode.IF_ICMPLE {
    public IF_ICMPLE(int targetPosition) {
        super(targetPosition);
    }

    @Override
    public Instruction execute(ThreadInfo ti) {

        StackFrame sf = ti.getModifiableTopFrame();

        IntegerExpression sym_v1 = (IntegerExpression) sf.getOperandAttr(1);
        IntegerExpression sym_v2 = (IntegerExpression) sf.getOperandAttr(0);

        if ((sym_v1 == null) && (sym_v2 == null)) { // both conditions are concrete
            // System.out.println("Execute IF_ICMPLE: The conditions are concrete");
            return super.execute(ti);
        } else { // at least one condition is symbolic
            ChoiceGenerator<?> cg;

            if (!ti.isFirstStepInsn()) { // first time around
                cg = new PCChoiceGenerator(SymbolicInstructionFactory.collect_constraints ? 1 : 2);
                ((PCChoiceGenerator) cg).setOffset(this.position);
                ((PCChoiceGenerator) cg).setMethodName(this.getMethodInfo().getFullName());
                ti.getVM().getSystemState().setNextChoiceGenerator(cg);
                return this;
            }
            cg = ti.getVM().getSystemState().getChoiceGenerator();
            assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;

            int v2 = sf.peek(0);
            int v1 = sf.peek(1);
            Instruction next_insn = super.execute(ti); // this also sets conditionValue
            if (SymbolicInstructionFactory.collect_constraints) {
                // YN: reuse conditionValue written from concrete exec + set choice correctly
                ((PCChoiceGenerator) cg).select(conditionValue ? 1 : 0);
            } else {
                conditionValue = (Integer) cg.getNextChoice() == 0 ? false : true;
            }

            PathCondition pc;

            // pc is updated with the pc stored in the choice generator above
            // get the path condition from the
            // previous choice generator of the same type

            ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);

            if (prev_cg == null)
                pc = new PathCondition();
            else
                pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();

            assert pc != null;

            if (conditionValue) {
                if (sym_v1 != null) {
                    if (sym_v2 != null) { // both are symbolic values
                        pc._addDet(Comparator.LE, sym_v1, sym_v2);
                    } else
                        pc._addDet(Comparator.LE, sym_v1, v2);
                } else
                    pc._addDet(Comparator.LE, v1, sym_v2);
                if (!pc.simplify()) {// not satisfiable
                    ti.getVM().getSystemState().setIgnored(true);
                } else {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                }
                return getTarget();
            } else {
                if (sym_v1 != null) {
                    if (sym_v2 != null) { // both are symbolic values
                        pc._addDet(Comparator.GT, sym_v1, sym_v2);
                    } else
                        pc._addDet(Comparator.GT, sym_v1, v2);
                } else
                    pc._addDet(Comparator.GT, v1, sym_v2);
                if (!pc.simplify()) {// not satisfiable
                    ti.getVM().getSystemState().setIgnored(true);
                } else {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                }
                return getNext(ti);
            }
        }
    }
}

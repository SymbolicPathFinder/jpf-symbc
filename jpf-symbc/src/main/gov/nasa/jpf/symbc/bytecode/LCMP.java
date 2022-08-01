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
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * Compare long ..., value1, value2 => ..., result
 * 
 * YN: fixed choice selection in symcrete support (Yannic Noller <nolleryc@gmail.com>)
 */
public class LCMP extends gov.nasa.jpf.jvm.bytecode.LCMP {

    @Override
    public Instruction execute(ThreadInfo th) {
        StackFrame sf = th.getModifiableTopFrame();

        IntegerExpression sym_v1 = (IntegerExpression) sf.getOperandAttr(1);
        IntegerExpression sym_v2 = (IntegerExpression) sf.getOperandAttr(3);

        if (sym_v1 == null && sym_v2 == null) // both conditions are concrete
            return super.execute(th);
        else { // at least one condition is symbolic

            ChoiceGenerator<?> cg;

            if (!th.isFirstStepInsn()) { // first time around
                cg = new PCChoiceGenerator(SymbolicInstructionFactory.collect_constraints ? 1 : 3);
                ((PCChoiceGenerator) cg).setOffset(this.position);
                ((PCChoiceGenerator) cg).setMethodName(this.getMethodInfo().getFullName());
                th.getVM().getSystemState().setNextChoiceGenerator(cg);
                return this;
            }
            long v1 = sf.popLong();
            long v2 = sf.popLong();

            int conditionValue = conditionValue(v1, v2);

            sf.push(conditionValue);

            cg = th.getVM().getSystemState().getChoiceGenerator();
            assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
            if (SymbolicInstructionFactory.collect_constraints) {
                // YN: reuse conditionValue written from concrete exec + set choice correctly
                ((PCChoiceGenerator) cg).select(conditionValue + 1);
            } else {
                conditionValue = ((PCChoiceGenerator) cg).getNextChoice() - 1;
            }

            PathCondition pc;

            // pc is updated with the pc stored in the choice generator above get
            // the path condition from the previous CG of the same type

            ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
            while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
                prev_cg = prev_cg.getPreviousChoiceGenerator();
            }

            if (prev_cg == null)
                pc = new PathCondition();
            else
                pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();
            assert pc != null;

            if (conditionValue == -1) {
                if (sym_v1 != null) {
                    if (sym_v2 != null) { // both are symbolic values
                        pc._addDet(Comparator.LT, sym_v2, sym_v1);
                    } else
                        pc._addDet(Comparator.LT, v2, sym_v1);
                } else
                    pc._addDet(Comparator.LT, sym_v2, v1);

                if (!pc.simplify()) {// not satisfiable
                    th.getVM().getSystemState().setIgnored(true);
                } else {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                }
            } else if (conditionValue == 0) {
                if (sym_v1 != null) {
                    if (sym_v2 != null) { // both are symbolic values
                        pc._addDet(Comparator.EQ, sym_v1, sym_v2);
                    } else
                        pc._addDet(Comparator.EQ, sym_v1, v2);
                } else
                    pc._addDet(Comparator.EQ, v1, sym_v2);
                if (!pc.simplify()) {// not satisfiable
                    th.getVM().getSystemState().setIgnored(true);
                } else {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                }
            } else { // 1
                if (sym_v1 != null) {
                    if (sym_v2 != null) { // both are symbolic values
                        pc._addDet(Comparator.GT, sym_v2, sym_v1);
                    } else
                        pc._addDet(Comparator.GT, (int) v2, sym_v1);
                } else
                    pc._addDet(Comparator.GT, sym_v2, (int) v1);
                if (!pc.simplify()) {// not satisfiable
                    th.getVM().getSystemState().setIgnored(true);
                } else {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                }
            }

            return getNext(th);
        }

    }

}

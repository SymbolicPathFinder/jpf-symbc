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

import gov.nasa.jpf.JPFException;
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
 * Access jump table by index and jump ..., index ...
 * 
 * YN: added symcrete support (Yannic Noller <nolleryc@gmail.com>)
 */
public class TABLESWITCH extends SwitchInstruction implements gov.nasa.jpf.vm.bytecode.TableSwitchInstruction {

    int min, max;

    public TABLESWITCH(int defaultTarget, int min, int max) {
        super(defaultTarget, (max - min + 1));
        this.min = min;
        this.max = max;
    }

    @Override
    public Instruction execute(ThreadInfo ti) {
        StackFrame sf = ti.getModifiableTopFrame();
        IntegerExpression sym_v = (IntegerExpression) sf.getOperandAttr();

        if (sym_v == null)
            return super.execute(ti);

        // the condition is symbolic
        ChoiceGenerator<?> cg;

        if (!ti.isFirstStepInsn()) { // first time around
            /* YN: added symcrete mode */
            // cg = new PCChoiceGenerator(targets.length+1);
            cg = new PCChoiceGenerator(SymbolicInstructionFactory.collect_constraints ? 1 : targets.length + 1);
            ((PCChoiceGenerator) cg).setOffset(this.position);
            ((PCChoiceGenerator) cg).setMethodName(this.getMethodInfo().getFullName());
            ti.getVM().getSystemState().setNextChoiceGenerator(cg);
            return this;
        } else { // this is what really returns results
            cg = ti.getVM().getSystemState().getChoiceGenerator();
            assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
        }
        sym_v = (IntegerExpression) sf.getOperandAttr();
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

        /* YN: enabling concolic exection */
        // int idx = (Integer)cg.getNextChoice();
        int idx;
        if (SymbolicInstructionFactory.collect_constraints) {
            // Check whether the value from the concrete execution is covered by the table switch or whether it should
            // trigger the default branch.
            if (value < 0 || value >= targets.length) {
                idx = targets.length; // default branch
            } else {
                idx = value;
            }
            ((PCChoiceGenerator) cg).select(idx);
        } else {
            idx = (Integer) cg.getNextChoice();
        }

        if (idx == targets.length) { // default branch
            lastIdx = -1;

            for (int i = 0; i < targets.length; i++)
                pc._addDet(Comparator.NE, sym_v._minus(min), i);
            // this could be replaced safely with only one constraint:
            // pc._addDet(Comparator.GT, sym_v._minus(min), targets.length);

            if (!pc.simplify()) {// not satisfiable
                ti.getVM().getSystemState().setIgnored(true);
            } else {
                ((PCChoiceGenerator) cg).setCurrentPC(pc);
            }
            return mi.getInstructionAt(target);
        } else {
            lastIdx = idx;
            pc._addDet(Comparator.EQ, sym_v._minus(min), idx);
            if (!pc.simplify()) {// not satisfiable
                ti.getVM().getSystemState().setIgnored(true);
            } else {
                ((PCChoiceGenerator) cg).setCurrentPC(pc);
            }
            return mi.getInstructionAt(targets[idx]);
        }

    }

    @Override
    protected Instruction executeConditional(ThreadInfo ti) {
        StackFrame sf = ti.getModifiableTopFrame();
        int value = sf.pop();
        int i = value - min;
        int pc;

        if (i >= 0 && i < targets.length) {
            lastIdx = i;
            pc = targets[i];
        } else {
            lastIdx = -1;
            pc = target;
        }

        // <2do> this is BAD - we should compute the target insns just once
        return mi.getInstructionAt(pc);
    }

    @Override
    public void setTarget(int value, int target) {

        int i = value - min;

        if (i >= 0 && i < targets.length) {
            targets[i] = target;
        } else {
            throw new JPFException("illegal tableswitch target: " + value);
        }
    }

    @Override
    public int getByteCode() {
        // TODO Auto-generated method stub
        return 0xAA;
    }

}

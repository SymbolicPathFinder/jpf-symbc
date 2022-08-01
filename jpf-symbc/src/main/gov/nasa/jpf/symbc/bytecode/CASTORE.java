/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * The Java Pathfinder core (jpf-core) platform is licensed under the
 * Apache License, Version 2.0 (the "License"); you may not use this file except
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

// author corina pasareanu corina.pasareanu@sv.cmu.edu

package gov.nasa.jpf.symbc.bytecode;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.ArrayIndexOutOfBoundsExecutiveException;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * Store into char array ..., arrayref, index, value => ...
 * 
 * YN: added symcrete support (Yannic Noller <nolleryc@gmail.com>)
 */
public class CASTORE extends gov.nasa.jpf.jvm.bytecode.CASTORE {
    
    public static int lastLength = -1; // YN: helper variable for last known length

    @Override
    public Instruction execute(ThreadInfo ti) {
        if (peekIndexAttr(ti) == null || !(peekIndexAttr(ti) instanceof IntegerExpression))
            return super.execute(ti);
        StackFrame frame = ti.getModifiableTopFrame();
        int arrayref = peekArrayRef(ti); // need to be polymorphic, could be LongArrayStore
        ElementInfo eiArray = ti.getElementInfo(arrayref);

        if (arrayref == MJIEnv.NULL) {
            return ti.createAndThrowException("java.lang.NullPointerException");
        }

        int len = (eiArray.getArrayFields()).arrayLength(); // assumed concrete
        lastLength = len; // YN: store last length

        if (!ti.isFirstStepInsn()) {
            PCChoiceGenerator arrayCG;

            if (SymbolicInstructionFactory.collect_constraints) {
                arrayCG = new PCChoiceGenerator(1); // YN: symcrete mode
            } else {
                arrayCG = new PCChoiceGenerator(0, len + 1); // add 2 error cases: <0, >=len
            }

            arrayCG.setOffset(this.position);
            arrayCG.setMethodName(this.getMethodInfo().getFullName());

            ti.getVM().getSystemState().setNextChoiceGenerator(arrayCG);

            // ti.reExecuteInstruction();
            if (SymbolicInstructionFactory.debugMode)
                System.out.println("# array cg registered: " + arrayCG);
            return this;

        } else { // this is what really returns results

            // index = frame.peek();
            PCChoiceGenerator lastCG = ti.getVM().getSystemState()
                    .getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
            assert (lastCG != null);
            PCChoiceGenerator prevCG = lastCG.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);

            if (SymbolicInstructionFactory.collect_constraints) {
                // YN: reuse index written from concrete exec + set choice correctly
                index = peekIndex(ti);
                ((PCChoiceGenerator) lastCG).select(index);
            } else {
                index = lastCG.getNextChoice();
            }

            IntegerExpression sym_index = (IntegerExpression) peekIndexAttr(ti);
            // check the constraint

            PathCondition pc;

            if (prevCG == null)
                pc = new PathCondition();
            else
                pc = ((PCChoiceGenerator) prevCG).getCurrentPC();

            assert pc != null;

            if (index < len) {
                pc._addDet(Comparator.EQ, index, sym_index);
                if (pc.simplify()) { // satisfiable
                    ((PCChoiceGenerator) lastCG).setCurrentPC(pc);
                } else {
                    ti.getVM().getSystemState().setIgnored(true);// backtrack
                    return getNext(ti);
                }
            }
            // now check for out of bounds exceptions
            else if (index == len) {
                pc._addDet(Comparator.LT, sym_index, 0);
                if (pc.simplify()) { // satisfiable
                    ((PCChoiceGenerator) lastCG).setCurrentPC(pc);
                    return ti.createAndThrowException("java.lang.ArrayIndexOutOfBoundsException");
                } else {
                    ti.getVM().getSystemState().setIgnored(true);// backtrack
                    return getNext(ti);
                }
            } else if (index == len + 1) {
                pc._addDet(Comparator.GE, sym_index, len);
                if (pc.simplify()) { // satisfiable
                    ((PCChoiceGenerator) lastCG).setCurrentPC(pc);
                    return ti.createAndThrowException("java.lang.ArrayIndexOutOfBoundsException");
                } else {
                    ti.getVM().getSystemState().setIgnored(true);// backtrack
                    return getNext(ti);
                }
            }

            // original code for concrete execution

            // int idx = peekIndex(ti);
            int aref = peekArrayRef(ti); // need to be polymorphic, could be LongArrayStore

            arrayOperandAttr = peekArrayAttr(ti);
            indexOperandAttr = peekIndexAttr(ti);

            // --- shared access CG
            /*
             * ignore POR for now TODO Scheduler scheduler = ti.getScheduler(); if
             * (scheduler.canHaveSharedArrayCG(ti, this, eiArray, idx)){ eiArray =
             * scheduler.updateArraySharedness(ti, eiArray, idx); if
             * (scheduler.setsSharedArrayCG(ti, this, eiArray, idx)){ return this; } } }
             */
            // System.out.println("len "+len+" index "+index);
            try {
                // setArrayElement(ti, frame, eiArray); // this pops operands
                int esize = getElementSize();
                Object attr = esize == 1 ? frame.getOperandAttr() : frame.getLongOperandAttr();

                popValue(frame);
                frame.pop();
                // don't set 'arrayRef' before we do the CG checks (would kill loop
                // optimization)
                arrayRef = frame.pop();

                eiArray = eiArray.getModifiableInstance();
                setField(eiArray, index);
                eiArray.setElementAttrNoClone(index, attr); // <2do> what if the value is the same but not the attr?

            } catch (ArrayIndexOutOfBoundsExecutiveException ex) { // at this point, the AIOBX is already processed
                return ex.getInstruction();
            }

            return getNext(ti);
        }
    }

}

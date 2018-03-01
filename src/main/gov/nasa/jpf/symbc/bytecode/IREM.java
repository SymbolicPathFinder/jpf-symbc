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

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * YN: fixed choice selection in symcrete support (Yannic Noller <nolleryc@gmail.com>)
 */
public class IREM extends gov.nasa.jpf.jvm.bytecode.IREM {

    @Override
    public Instruction execute(ThreadInfo th) {
        StackFrame sf = th.getModifiableTopFrame();
        IntegerExpression sym_v1 = (IntegerExpression) sf.getOperandAttr(0);
        int v1 = sf.peek(0);
        IntegerExpression sym_v2 = (IntegerExpression) sf.getOperandAttr(1);
        int v2 = sf.peek(1);
        if (v1 == 0)
            return th.createAndThrowException("java.lang.ArithmeticException", "div by 0");

        if (sym_v1 == null) {
            Instruction next_insn = super.execute(th);
            if (sym_v2 != null) // result is symbolic expression
                sf.setOperandAttr(sym_v2._rem(v1));
            return next_insn;
        }

        // div by zero check affects path condition
        // sym_v1 is non-null and should be checked against zero

        ChoiceGenerator<?> cg;
        boolean condition;

        if (!th.isFirstStepInsn()) { // first time around
            cg = new PCChoiceGenerator(SymbolicInstructionFactory.collect_constraints ? 1 : 2);
            ((PCChoiceGenerator) cg).setOffset(this.position);
            ((PCChoiceGenerator) cg).setMethodName(this.getMethodInfo().getFullName());
            th.getVM().setNextChoiceGenerator(cg);
            return this;
        } else { // this is what really returns results
            cg = th.getVM().getChoiceGenerator();
            assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;

            if (SymbolicInstructionFactory.collect_constraints) {
                condition = v1 == 0; // i.e. false
                ((PCChoiceGenerator) cg).select(condition ? 1 : 0); // YN: set the choice correctly
            } else {
                condition = (Integer) cg.getNextChoice() == 0 ? false : true;
            }

        }

        super.execute(th); // pops v1, v2 and pushes r = v2 % v1;

        PathCondition pc;
        ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);

        if (prev_cg == null)
            pc = new PathCondition();
        else
            pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();

        assert pc != null;

        if (condition) { // check div by zero
            pc._addDet(Comparator.EQ, sym_v1, 0);
            if (pc.simplify()) { // satisfiable
                ((PCChoiceGenerator) cg).setCurrentPC(pc);

                return th.createAndThrowException("java.lang.ArithmeticException", "rem by 0");
            } else {
                th.getVM().getSystemState().setIgnored(true);
                return getNext(th);
            }
        } else {
            pc._addDet(Comparator.NE, sym_v1, 0);
            if (pc.simplify()) { // satisfiable
                ((PCChoiceGenerator) cg).setCurrentPC(pc);

                // set the result
                IntegerExpression result;
                if (sym_v2 != null)
                    result = sym_v2._rem(sym_v1);
                else
                    result = sym_v1._rem_reverse(v2);

                sf = th.getModifiableTopFrame();
                sf.setOperandAttr(result);
                return getNext(th);

            } else {
                th.getVM().getSystemState().setIgnored(true);
                return getNext(th);
            }
        }

    }
}

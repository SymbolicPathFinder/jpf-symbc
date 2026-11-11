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

package gov.nasa.jpf.symbc.bytecode.symarrays;


import gov.nasa.jpf.symbc.arrays.ArrayExpression;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.string.SymbolicLengthInteger;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.string.SymbolicLengthInteger;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ClassLoaderInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.Heap;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.IntVariable;

import java.util.ArrayList;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.AdapterSynth.SPFAdapterSynth.getVal;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil.maybeParseConstraint;

/**
 * Symbolic version of the NEWARRAY class from jpf-core. Has some extra code to
 * detect if a symbolic variable is being used as the size of the new array, and
 * treat it accordingly.
 * <p>
 * Someone with more experience should review this :)
 * TODO: to review; Corina: this code does not make too much sense: for now I will comment it out
 * who wrote it?
 */

public class NEWARRAY extends gov.nasa.jpf.jvm.bytecode.NEWARRAY {

    private static final int c = 0;//TODO make this into a configuration option
    private static final boolean stopIfCExceeded = false; //TODO make this into a configuration option
    private static final int[] smallValues = {3};//,3,4,5}; //, 10};
    ArrayList<Long> values;

    public NEWARRAY(int typeCode) {
        super(typeCode);
    }

    @Override
    public Instruction execute(ThreadInfo ti) {

        StackFrame sf = ti.getModifiableTopFrame();
        Object attr = sf.getOperandAttr();
        ArrayExpression arrayAttr = null;
        PathCondition pc = null;
        ;

      /*  if(attr instanceof SymbolicLengthInteger || attr instanceof IntegerExpression)
            return ti.createAndThrowException("java.lang.NegativeArraySizeException");
*/
        if (attr instanceof SymbolicLengthInteger) {
            long l = ((SymbolicLengthInteger) attr).solution;
//			assert(l>=0 && l<=Integer.MAX_VALUE) : "Array length must be positive integer";
            if (!(l >= 0 && l <= Integer.MAX_VALUE))
                return ti.createAndThrowException("java.lang.NegativeArraySizeException");
            arrayLength = (int) l;
            sf.pop();
        } else if (attr instanceof IntegerExpression) {
//            return ti.createAndThrowException("unsupported creation of symbolic array length.");
            ChoiceGenerator<?> cg = null;
            if (!ti.isFirstStepInsn()) {
                /* These changes are introduced by Java Ranger's path-merging in SPF */
                if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
                    pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
                } else {
                    pc = new PathCondition();
                    pc._addDet(Comparator.EQ, new IntegerConstant(0), new IntegerConstant(0));
                }
                assert pc != null;

                String name = attr instanceof SymbolicInteger ? ((SymbolicInteger) attr).getName() : null;
                if (attr instanceof BinaryNonLinearIntegerExpression) {
                    // if attr is BNLIE with same operands, concretize the operand to avoid reasoning over the non-linear arithmetic
                    BinaryNonLinearIntegerExpression attrBNLIE = (BinaryNonLinearIntegerExpression) attr;
                    if (attrBNLIE.left instanceof SymbolicInteger && attrBNLIE.right instanceof SymbolicInteger
                            && attrBNLIE.left.equals(attrBNLIE.right)) {
                        name = ((SymbolicInteger) attrBNLIE.left).getName();
                        attr = attrBNLIE.left;
                    }
                }
                if (name == null) {
                    ti.getVM().getSystemState().setIgnored(true);
                    return getNext(ti);
                }

                values = new ArrayList<>();

                for (int i = 0; i < smallValues.length; i++) {
                    PathCondition newPC = pc.make_copy();
                    newPC._addDet(Comparator.EQ, (IntegerExpression) attr, new IntegerConstant(smallValues[i]));
                    Map<String, Object> map = newPC.solveWithValuation((SymbolicInteger) attr, null);
                    Long lastValue = getVal(map, name);
                    if (map == null || map.size() == 0 || lastValue == null) continue;
                    else if (lastValue == smallValues[i]) values.add(lastValue);
                }
                //SH: for now do not support any symbolic length array, that is outside the range of smallValues. TODO: extend that to support symbolic array length.
                if (values.size() == 0)
                    throw new RuntimeException("unsupported symbolic size of array length.");

                // First choice is to explore negative array length
                // Last choice is to explore unconstrained symbolic array length
                // All the choices in the middle explore small array lengths -- SH: commenting this option out as of now, since it is broken. TODO
                cg = new PCChoiceGenerator(values.size() + 1); // only one choice in addition to the values to be explored setup as of now
                /* End of Java Ranger changes */

//                cg = new PCChoiceGenerator(2);
                ti.getVM().setNextChoiceGenerator(cg);
                return this;
            }
            cg = ti.getVM().getSystemState().getChoiceGenerator();
            assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got:" + cg;
//                sf.pop();
//                arrayLength = Math.toIntExact(values.get((Integer)cg.getNextChoice()));


            ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);

            if (prev_cg == null)
                pc = new PathCondition();
            else
                pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();
            assert pc != null;

            if ((Integer) cg.getNextChoice() == 0) {
                pc._addDet(Comparator.LT, getBNLIEOperand((IntegerExpression) attr), new IntegerConstant(0));
                if (pc.simplify()) {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                    return ti.createAndThrowException("java.lang.NegativeArraySizeException");
//                    sf.pop();
//                    arrayLength = 1;
                } else {
                    ti.getVM().getSystemState().setIgnored(true);
                    return getNext(ti);
                }
            } else { // exploring smallValues choices.
//                if ((Integer) cg.getNextChoice() < cg.getTotalNumberOfChoices() - 1) {
                pc._addDet(Comparator.GE, getBNLIEOperand((IntegerExpression) attr), new IntegerConstant(0));
                if (pc.simplify()) {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                    arrayLength = sf.pop();
                } else {
                    ti.getVM().getSystemState().setIgnored(true);
                    return getNext(ti);
                }
                arrayLength = Math.toIntExact(values.get((Integer) cg.getNextChoice() - 1));
                pc._addDet(Comparator.EQ, getBNLIEOperand((IntegerExpression) attr), new IntegerConstant(arrayLength));
            }
            /*else if ((Integer) cg.getNextChoice() == cg.getTotalNumberOfChoices() - 1) {
                pc._addDet(Comparator.GE, (IntegerExpression) attr, new IntegerConstant(0));
                if (pc.simplify()) {
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                    arrayLength = sf.pop();
                } else {
                    ti.getVM().getSystemState().setIgnored(true);
                    return getNext(ti);
                }
            }*/
        } else {
            arrayLength = sf.pop();
        }

        //the remainder of the code is almost identical to the parent class

        Heap heap = ti.getHeap();

        if (arrayLength < 0) {
            return ti.createAndThrowException("java.lang.NegativeArraySizeException");
        }

        // there is no clinit for array classes, but we still have  to create a class object
        // since its a builtin class, we also don't have to bother with NoClassDefFoundErrors
        String clsName = "[" + type;

        ClassInfo ci = ClassLoaderInfo.getCurrentResolvedClassInfo(clsName);
        if (!ci.isRegistered()) {
            ci.registerClass(ti);
            ci.setInitialized();
        }

        if (heap.isOutOfMemory()) { // simulate OutOfMemoryError
            return ti.createAndThrowException("java.lang.OutOfMemoryError",
                    "trying to allocate new " +
                            getTypeName() +
                            "[" + arrayLength + "]");
        }

        ElementInfo eiArray = heap.newArray(type, arrayLength, ti);
        int arrayRef = eiArray.getObjectRef();

        sf.pushRef(arrayRef);

        if (attr instanceof IntegerExpression) {
            arrayAttr = new ArrayExpression(eiArray.toString());
            pc._addDet(Comparator.EQ, arrayAttr.length, (IntegerExpression) attr);
            pc.arrayExpressions.put(arrayAttr.getRootName(), arrayAttr);
            try {
                maybeParseConstraint(pc);
            } catch (StaticRegionException e) {
                return ti.createAndThrowException("Failed to send arrayAttr.length constraint to solver");
            }
        }
        sf.setOperandAttr(arrayAttr);

        ti.getVM().getSystemState().checkGC(); // has to happen after we push the new object ref

        return getNext(ti);

    }

    private IntegerExpression getBNLIEOperand(IntegerExpression attr) {
        if (!(attr instanceof BinaryNonLinearIntegerExpression)) return attr;
        BinaryNonLinearIntegerExpression attrBNLIE = (BinaryNonLinearIntegerExpression) attr;
        if (attrBNLIE.left instanceof SymbolicInteger && attrBNLIE.right instanceof SymbolicInteger
                && attrBNLIE.left.equals(attrBNLIE.right)) {
            return attrBNLIE.left;
        }
        assert (false);
        return null;
    }

}

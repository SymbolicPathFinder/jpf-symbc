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

// author Aymeric Fromherz aymeric.fromherz@ens.fr

package gov.nasa.jpf.symbc.bytecode.symarrays;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;

import gov.nasa.jpf.symbc.arrays.ArrayExpression;
import gov.nasa.jpf.symbc.arrays.ArrayHeapNode;
import gov.nasa.jpf.symbc.arrays.HelperResult;
import gov.nasa.jpf.symbc.arrays.SelectExpression;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.vm.ArrayFields;
import gov.nasa.jpf.vm.ArrayIndexOutOfBoundsExecutiveException;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ClassLoaderInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.Scheduler;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * Load reference from array
 * ..., arrayref, index  => ..., value
 */
public class AALOAD extends gov.nasa.jpf.jvm.bytecode.AALOAD {

	
  @Override
  public Instruction execute (ThreadInfo ti) {

      ArrayExpression arrayAttr = null;
      ArrayHeapNode[] prevSymRefs = null; // previously initialized objects of same type
      int numSymRefs = 0; // number of previously initialized objects
      ChoiceGenerator<?> prevHeapCG = null;
      ChoiceGenerator<?> cg;
      int currentChoice;
      IntegerExpression indexAttr = null;
   	  StackFrame frame = ti.getModifiableTopFrame();
	  arrayRef = frame.peek(1); // ..,arrayRef,idx

      if (arrayRef == MJIEnv.NULL) {
          return ti.createAndThrowException("java.lang.NullPointerException");
      }

      // Retrieve the array expression if it was previously in the pathcondition
      PCChoiceGenerator temp_cg = (PCChoiceGenerator)ti.getVM().getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
      if (temp_cg != null) {
          // There was a previous pathcondition
          if (temp_cg.getCurrentPC().arrayExpressions.containsKey(ti.getElementInfo(ti.getModifiableTopFrame().peek(1)).toString())) {
              // The array was previously in the path condition, we retrieve the symbolic element
              ti.getModifiableTopFrame().setOperandAttr(1, temp_cg.getCurrentPC().arrayExpressions.get(ti.getElementInfo(ti.getModifiableTopFrame().peek(1)).toString()));
          }
      }
	
      if (peekArrayAttr(ti) == null || !(peekArrayAttr(ti) instanceof ArrayExpression)) {
          // In this case, the array isn't symbolic
          if (peekIndexAttr(ti) == null || !(peekIndexAttr(ti) instanceof IntegerExpression)) {
              // In this case, the index isn't symbolic either
              return super.execute(ti);
          }
          // We have a concrete array, but a symbolic index. We add all the constraints about the elements of the array and perform the select
          // We will need to get information about the type of the elements as well
          // We need to add the information in PC after it is declared.
          ElementInfo arrayInfo = ti.getElementInfo(arrayRef);
          if (!ti.isFirstStepInsn()) { // first time around
              cg = new PCChoiceGenerator(arrayInfo.arrayLength() + 2);
              ((PCChoiceGenerator)cg).setOffset(this.position);
              ((PCChoiceGenerator)cg).setMethodName(this.getMethodInfo().getFullName());
              ti.getVM().setNextChoiceGenerator(cg);
              return this;
          } else { // this is what really returns results
              cg = ti.getVM().getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
              assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
              currentChoice = (Integer)cg.getNextChoice();
          }

          PathCondition pc;
          ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);

          if (prev_cg == null)
              pc = new PathCondition();
          else
              pc = ((PCChoiceGenerator)prev_cg).getCurrentPC();

          assert pc != null;
          indexAttr = ((IntegerExpression)peekIndexAttr(ti));

          if (currentChoice < arrayInfo.arrayLength()) {
            // For each possible index, we check if the symbolic index can be equal to it. If so, we return the value at this index

            pc._addDet(Comparator.EQ, indexAttr, new IntegerConstant(currentChoice));
            if (pc.simplify()) { // satisfiable
                frame.pop(2);
                arrayInfo.checkArrayBounds(currentChoice); // should not fail
                int value = arrayInfo.getReferenceElement(currentChoice);
                frame.pushRef(value);
                Object elementAttr = arrayInfo.getElementAttr(currentChoice);
                if (elementAttr != null) {
                    frame.setOperandAttr(elementAttr);
                }
                return getNext(ti);
            } else {
                ti.getVM().getSystemState().setIgnored(true);
                return getNext(ti);
            }
          } else if (currentChoice == arrayInfo.arrayLength()) {
              // We check if we can be out of bounds (greater than the length)
              pc._addDet(Comparator.GE, indexAttr, new IntegerConstant(arrayInfo.arrayLength()));
              if (pc.simplify()) { // satisfiable
                  ((PCChoiceGenerator) cg).setCurrentPC(pc);
                  return ti.createAndThrowException("java.lang.ArrayIndexOutOfBoundsException", "index greater than array bounds");
              } else {
                  ti.getVM().getSystemState().setIgnored(true);
                  return getNext(ti);
              }
          } else if (currentChoice == arrayInfo.arrayLength() +1) {
              // We check if we can be out of bounds (smaller than 0)
              pc._addDet(Comparator.LT, indexAttr, new IntegerConstant(0));
              if (pc.simplify()) { // satisfiable
                  ((PCChoiceGenerator) cg).setCurrentPC(pc);
                  return ti.createAndThrowException("java.lang.ArrayIndexOutOfBoundsException", "index smaller than array bounds");
              } else {
                  ti.getVM().getSystemState().setIgnored(true);
                  return getNext(ti);
              }
          } else {
              throw new RuntimeException("We shouldn't end here in AALOAD");
          }
       } else {
           arrayAttr = (ArrayExpression)peekArrayAttr(ti);
       }
	  
      String typeElemArray = arrayAttr.getElemType();

      if (typeElemArray.equals("?")) {
            throw new RuntimeException("Type of array elements unknown");
      }

      ClassInfo typeClassInfo = ClassLoaderInfo.getCurrentResolvedClassInfo(typeElemArray);

      ChoiceGenerator<?> thisHeapCG;

      if (!ti.isFirstStepInsn()) {
          // We add the HeapChoiceGenerator that will be required if we can load an element
          numSymRefs = 0;
          prevSymRefs = null;
          prevHeapCG = ti.getVM().getLastChoiceGeneratorOfType(HeapChoiceGenerator.class);

          if (prevHeapCG != null) {
              SymbolicInputHeap symInputHeap = ((HeapChoiceGenerator)prevHeapCG).getCurrentSymInputHeap();
              // We get only the previously initialized elements for this array
              prevSymRefs = symInputHeap.getArrayNodesOfType(typeClassInfo, arrayRef);
              numSymRefs = prevSymRefs.length;
          }

          int increment = 2;
          if (typeClassInfo.isAbstract()) {
               increment = 1;
          }
          thisHeapCG = new HeapChoiceGenerator(numSymRefs + increment);
          ti.getVM().setNextChoiceGenerator(thisHeapCG);  

          // We now add the PCChoiceGenerator that will be used first to detemrine if we are in bounds
          cg = new PCChoiceGenerator(3);
          ((PCChoiceGenerator)cg).setOffset(this.position);
          ((PCChoiceGenerator)cg).setMethodName(this.getMethodInfo().getFullName());
          ti.getVM().setNextChoiceGenerator(cg);
          return this;
      } else {
          cg = ti.getVM().getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
          thisHeapCG = ti.getVM().getLastChoiceGeneratorOfType(HeapChoiceGenerator.class);
          assert (thisHeapCG instanceof HeapChoiceGenerator) : "expected HeapChoiceGenerator, got: " + thisHeapCG;
          assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
          currentChoice = (Integer)cg.getNextChoice();
      }

      PathCondition pc;
      ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);

      if (prev_cg == null)
          pc = new PathCondition();
      else
          pc = ((PCChoiceGenerator)prev_cg).getCurrentPC();

      if (pc.arrayExpressions.containsKey(arrayAttr.getRootName())) {
         arrayAttr = (ArrayExpression)pc.arrayExpressions.get(arrayAttr.getRootName());
      }

      assert pc != null;
      if (peekIndexAttr(ti) == null || !(peekIndexAttr(ti) instanceof IntegerExpression)) {
          // The index is not symbolic
          index = frame.peek();
          indexAttr = new IntegerConstant(index);
      } else {
          indexAttr = (IntegerExpression)peekIndexAttr(ti);
      }
       
      if (currentChoice == 1) {
        pc._addDet(Comparator.LT, indexAttr, new IntegerConstant(0));
        if (pc.simplify()) { // satisfiable
            ((PCChoiceGenerator) cg).setCurrentPC(pc);
            return ti.createAndThrowException("java.lang.ArrayIndexOutOfBoundsException", "index smaller than array bounds");
        } else {
            ti.getVM().getSystemState().setIgnored(true);
            return getNext(ti);
        }
      } else if (currentChoice == 2) {
          pc._addDet(Comparator.GE, indexAttr, arrayAttr.length);
          if (pc.simplify()) { // satisfiable
              ((PCChoiceGenerator) cg).setCurrentPC(pc);
              return ti.createAndThrowException("java.lang.ArrayIndexOutOfBoundsException", "index greater than array bounds");
          } else {
              ti.getVM().getSystemState().setIgnored(true);
              return getNext(ti);
          }
      } else {
          pc._addDet(Comparator.LT, indexAttr, arrayAttr.length);
          pc._addDet(Comparator.GE, indexAttr, new IntegerConstant(0));
          PathCondition pcHeap;
          SymbolicInputHeap symInputHeap;

          prevHeapCG = thisHeapCG.getPreviousChoiceGeneratorOfType(HeapChoiceGenerator.class);

          if (prevHeapCG == null) {
              pcHeap = new PathCondition();
              symInputHeap = new SymbolicInputHeap();
          } else {
              pcHeap = ((HeapChoiceGenerator)prevHeapCG).getCurrentPCheap();
              symInputHeap = ((HeapChoiceGenerator) prevHeapCG).getCurrentSymInputHeap();
          }

          assert pcHeap != null;
          assert symInputHeap != null;

          SelectExpression se = null;

          if (peekIndexAttr(ti) == null || !(peekIndexAttr(ti) instanceof IntegerExpression)) {
              // In this case the index isn't symbolic
              index = frame.peek();
              indexAttr = new IntegerConstant(index);
          } else {
              indexAttr = (IntegerExpression)peekIndexAttr(ti);
          }
          assert arrayAttr != null;
          assert indexAttr != null;

          int daIndex = 0; // index into JPF's dynamic area
          currentChoice = ((HeapChoiceGenerator) thisHeapCG).getNextChoice();

          if (currentChoice < numSymRefs) {
            // We load a previously initialized object
            ArrayHeapNode candidateNode = prevSymRefs[currentChoice];
            pc._addDet(Comparator.EQ, indexAttr, candidateNode.arrayIndex);
            // The index is the same than the previous one
            se = new SelectExpression(arrayAttr, indexAttr);
            pc._addDet(Comparator.EQ, se, candidateNode.getSymbolic());
            if (pc.simplify()) {
                pc.arrayExpressions.put(arrayAttr.getRootName(), arrayAttr);
                daIndex = candidateNode.getIndex();
                frame.pop(2); // We pop the array and the index
                frame.push(daIndex, true); // We have instantiated an object, and added the constraints in the PC

                ((PCChoiceGenerator) cg).setCurrentPC(pc);
                ((HeapChoiceGenerator)thisHeapCG).setCurrentPCheap(pcHeap);
                ((HeapChoiceGenerator)thisHeapCG).setCurrentSymInputHeap(symInputHeap);
                return getNext(ti);
            } else {
                ti.getVM().getSystemState().setIgnored(true);
                return getNext(ti);
            }
          } else if (currentChoice == (numSymRefs)) { // null object
            se = new SelectExpression(arrayAttr, indexAttr);
            pc._addDet(Comparator.EQ, se, new IntegerConstant(-1));
            if (pc.simplify()) { // satisfiable
                pc.arrayExpressions.put(arrayAttr.getRootName(), arrayAttr);
                daIndex = MJIEnv.NULL;
                frame.pop(2); // We pop the index and the array;
                frame.push(daIndex, true);

                ((PCChoiceGenerator) cg).setCurrentPC(pc);
                ((HeapChoiceGenerator)thisHeapCG).setCurrentPCheap(pcHeap);
                ((HeapChoiceGenerator)thisHeapCG).setCurrentSymInputHeap(symInputHeap);
                return getNext(ti);
            } else {
                ti.getVM().getSystemState().setIgnored(true);
                return getNext(ti);
            }
          } else {
                HelperResult hpResult = Helper.addNewArrayHeapNode(typeClassInfo, ti, arrayAttr, pcHeap, symInputHeap, numSymRefs, prevSymRefs, false, indexAttr, arrayRef);
                daIndex = hpResult.idx;
                HeapNode candidateNode = hpResult.n;
                // Since the object is different from all the previously initialized ones, we don't need to add constraints
                // on the index, it will be inferred from Z3 array theory
                se = new SelectExpression(arrayAttr, indexAttr);
                pc._addDet(Comparator.EQ, se, candidateNode.getSymbolic());
              if (pc.simplify()) { // satisfiable
                pc.arrayExpressions.put(arrayAttr.getRootName(), arrayAttr);

                frame.pop(2); // We pop the array and the index
                frame.push(daIndex, true);

                ((PCChoiceGenerator) cg).setCurrentPC(pc);
                ((HeapChoiceGenerator) thisHeapCG).setCurrentPCheap(pcHeap);
                ((HeapChoiceGenerator) thisHeapCG).setCurrentSymInputHeap(symInputHeap);
                return getNext(ti);
              } else {
                  ti.getVM().getSystemState().setIgnored(true);
                  return getNext(ti);
              }
          }   
      }
    }
}

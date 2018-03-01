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

import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.arrays.ArrayExpression;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.SymbolicStringBuilder;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ClassLoaderInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.KernelState;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.SystemState;
//import gov.nasa.jpf.symbc.uberlazy.TypeHierarchy;
import gov.nasa.jpf.vm.ThreadInfo;

// Corina: I need to add the latest fix from the v6 to treat properly "this"

public class ALOAD extends gov.nasa.jpf.jvm.bytecode.ALOAD {

	public ALOAD(int localVarIndex) {
	    super(localVarIndex);
	}

	
    //private int numNewRefs = 0; // # of new reference objects to account for polymorphism -- work of Neha Rungta -- needs to be updated
      boolean abstractClass = false;

    @Override
	public Instruction execute (ThreadInfo th) {
		HeapNode[] prevSymRefs = null; // previously initialized objects of same type: candidates for lazy init
        int numSymRefs = 0; // # of prev. initialized objects
        ChoiceGenerator<?> prevHeapCG = null;

		Config conf = th.getVM().getConfig();
		String[] lazy = conf.getStringArray("symbolic.lazy");
		if (lazy == null || !lazy[0].equalsIgnoreCase("true"))
			return super.execute(th);

		// TODO: fix handle polymorphism
		

		StackFrame sf = th.getModifiableTopFrame();
		int objRef = sf.peek();
		ElementInfo ei = th.getElementInfo(objRef);
		Object attr = sf.getLocalAttr(index);
		String typeOfLocalVar = super.getLocalVariableType();


		if(attr == null || typeOfLocalVar.equals("?") || attr instanceof SymbolicStringBuilder || attr instanceof StringExpression || attr instanceof ArrayExpression) {
			return super.execute(th);
		}
		
		ClassInfo typeClassInfo = ClassLoaderInfo.getCurrentResolvedClassInfo(typeOfLocalVar);

		int currentChoice;
		ChoiceGenerator<?> thisHeapCG;
		
		if(!th.isFirstStepInsn()) {
			//System.out.println("the first time");

			prevSymRefs = null;
			numSymRefs = 0;
			prevHeapCG = null;

			prevHeapCG = th.getVM().getLastChoiceGeneratorOfType(HeapChoiceGenerator.class);

			if (prevHeapCG != null) {
				// determine # of candidates for lazy initialization
				SymbolicInputHeap symInputHeap =
					((HeapChoiceGenerator)prevHeapCG).getCurrentSymInputHeap();

				prevSymRefs = symInputHeap.getNodesOfType(typeClassInfo);
                numSymRefs = prevSymRefs.length;

			}
			int increment = 2;
			if(typeClassInfo.isAbstract() || (((IntegerExpression)attr).toString()).contains("this")) {
				 abstractClass = true;
				 increment = 1; // only null for abstract, non null for this
			}
			
			// TODO fix: subtypes

				thisHeapCG = new HeapChoiceGenerator(numSymRefs+increment);  //+null,new
			
			th.getVM().setNextChoiceGenerator(thisHeapCG);
			return this;
		} else { 
			//this is what returns the results
			thisHeapCG = th.getVM().getChoiceGenerator();
			assert(thisHeapCG instanceof HeapChoiceGenerator) :
				"expected HeapChoiceGenerator, got:" + thisHeapCG;
			currentChoice = ((HeapChoiceGenerator) thisHeapCG).getNextChoice();
		}

		PathCondition pcHeap;
		SymbolicInputHeap symInputHeap;

        prevHeapCG = thisHeapCG.getPreviousChoiceGeneratorOfType(HeapChoiceGenerator.class);

		
		if(prevHeapCG == null) {
			pcHeap = new PathCondition();
			symInputHeap = new SymbolicInputHeap();
		} else {
			pcHeap =  ((HeapChoiceGenerator) prevHeapCG).getCurrentPCheap();
			symInputHeap = ((HeapChoiceGenerator) prevHeapCG).getCurrentSymInputHeap();
		}

		assert pcHeap != null;
		assert symInputHeap != null;
		
		prevSymRefs = symInputHeap.getNodesOfType(typeClassInfo);
        numSymRefs = prevSymRefs.length;

		int daIndex = 0; //index into JPF's dynamic area

		if (currentChoice < numSymRefs) { // lazy initialization using a previously lazily initialized object
			HeapNode candidateNode = prevSymRefs[currentChoice];
			// here we should update pcHeap with the constraint attr == candidateNode.sym_v
			pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, candidateNode.getSymbolic());
			daIndex = candidateNode.getIndex();
		}
		else if (currentChoice == numSymRefs && !(((IntegerExpression)attr).toString()).contains("this")){ //null object
			pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, new IntegerConstant(-1));
			daIndex = MJIEnv.NULL;
		}
		else if ((currentChoice == (numSymRefs + 1) && !abstractClass) | (currentChoice == numSymRefs && (((IntegerExpression)attr).toString()).contains("this"))) {
			//creates a new object with all fields symbolic
			boolean shared = (ei == null? false: ei.isShared());
			daIndex = Helper.addNewHeapNode(typeClassInfo, th, attr, pcHeap,
							symInputHeap, numSymRefs, prevSymRefs, shared);
		} else {
			//TODO: fix subtypes
			System.err.println("subtypes not handled");
		}


		sf.setLocalVariable(index, daIndex, true);
		sf.setLocalAttr(index, null);
		sf.push(daIndex, true);

		((HeapChoiceGenerator)thisHeapCG).setCurrentPCheap(pcHeap);
		((HeapChoiceGenerator)thisHeapCG).setCurrentSymInputHeap(symInputHeap);
		if (SymbolicInstructionFactory.debugMode)
			System.out.println("ALOAD pcHeap: " + pcHeap);
		return getNext(th);
	}

}

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
import gov.nasa.jpf.JPFException;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.SymbolicStringBuilder;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.LoadOnJPFRequired;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.StackFrame;
//import gov.nasa.jpf.symbc.uberlazy.TypeHierarchy;
import gov.nasa.jpf.vm.ThreadInfo;

public class GETSTATIC extends gov.nasa.jpf.jvm.bytecode.GETSTATIC {
	public GETSTATIC(String fieldName, String clsName, String fieldDescriptor){
	    super(fieldName, clsName, fieldDescriptor);
	  }

	//private int numNewRefs = 0; // # of new reference objects to account for polymorphism -- work of Neha Rungta -- needs to be updated
	 
	boolean abstractClass = false;


	@Override
	public Instruction execute (ThreadInfo ti) {
	   
		ChoiceGenerator<?> prevHeapCG = null;
		HeapNode[] prevSymRefs = null;
		int numSymRefs = 0;
		
		Config conf = ti.getVM().getConfig();
		String[] lazy = conf.getStringArray("symbolic.lazy");
		if (lazy == null || !lazy[0].equalsIgnoreCase("true"))
			return super.execute(ti);

	    ClassInfo ciField;
	    FieldInfo fieldInfo;
	    
	    try {
	      fieldInfo = getFieldInfo();
	    } catch(LoadOnJPFRequired lre) {
	      return ti.getPC();
	    }
	    
	    if (fieldInfo == null) {
	      return ti.createAndThrowException("java.lang.NoSuchFieldError",
	          (className + '.' + fname));
	    }
		
		ciField = fieldInfo.getClassInfo();
	    
	    if (!mi.isClinit(ciField) && ciField.initializeClass(ti)) {
	      // note - this returns the next insn in the topmost clinit that just got pushed
	      return ti.getPC();
	    }

	    ElementInfo ei = ciField.getModifiableStaticElementInfo();
	    //ei = ei. getInstanceWithUpdatedSharedness(ti); POR broken again

	    if (ei == null){
	      throw new JPFException("attempt to access field: " + fname + " of uninitialized class: " + ciField.getName());
	    }

		Object attr = ei.getFieldAttr(fi);

		if (!(fi.isReference() && attr != null))
			return super.execute(ti);

		if(attr instanceof StringExpression || attr instanceof SymbolicStringBuilder)
				return super.execute(ti); // Strings are handled specially

		
		// else: lazy initialization
		if (SymbolicInstructionFactory.debugMode)
			  System.out.println("lazy initialization");
		
		// may introduce thread choices
		//POR broken again
		 //if (isNewPorFieldBoundary(ti)) {
		   //   if (createAndSetSharedFieldAccessCG( ei, ti)) {
		        //return this; // not yet because well create the heap cg
		     // }
		    //}  
		   

		int currentChoice;
		ChoiceGenerator<?> heapCG;

		ClassInfo typeClassInfo = fi.getTypeClassInfo(); // use this instead of fullType


		// first time around
		
		if (!ti.isFirstStepInsn()) {
			prevSymRefs = null;
			numSymRefs = 0;
			
			prevHeapCG = ti.getVM().getSystemState().getLastChoiceGeneratorOfType(HeapChoiceGenerator.class);

			if (prevHeapCG != null) {
					// collect candidates for lazy initialization
					  SymbolicInputHeap symInputHeap =
						  ((HeapChoiceGenerator)prevHeapCG).getCurrentSymInputHeap();

					  prevSymRefs = symInputHeap.getNodesOfType(typeClassInfo);
					  numSymRefs = prevSymRefs.length;
					  
			}
			
			// TODO: fix subtypes
            heapCG = new HeapChoiceGenerator(numSymRefs+2);  //+null,new
			ti.getVM().getSystemState().setNextChoiceGenerator(heapCG);
			return this;
		} else {  // this is what really returns results
			heapCG = ti.getVM().getSystemState().getLastChoiceGeneratorOfType(HeapChoiceGenerator.class);
			assert (heapCG !=null && heapCG instanceof HeapChoiceGenerator) :
				  "expected HeapChoiceGenerator, got: " + heapCG;
			currentChoice = ((HeapChoiceGenerator)heapCG).getNextChoice();
		}

		
		PathCondition pcHeap; //this pc contains only the constraints on the heap
		SymbolicInputHeap symInputHeap;

		// pcHeap is updated with the pcHeap stored in the choice generator above
		// get the pcHeap from the previous choice generator of the same type
		
		prevHeapCG = heapCG.getPreviousChoiceGeneratorOfType(HeapChoiceGenerator.class);

		if (prevHeapCG == null){
			pcHeap = new PathCondition();
			symInputHeap = new SymbolicInputHeap();
		}
		else {
			pcHeap = ((HeapChoiceGenerator)prevHeapCG).getCurrentPCheap();
			symInputHeap = ((HeapChoiceGenerator)prevHeapCG).getCurrentSymInputHeap();
		}
		assert pcHeap != null;
		assert symInputHeap != null;

		 prevSymRefs = symInputHeap.getNodesOfType(typeClassInfo);
         numSymRefs = prevSymRefs.length;
		

		int daIndex = 0; //index into JPF's dynamic area
		if (currentChoice < numSymRefs) { // lazy initialization
			  HeapNode candidateNode = prevSymRefs[currentChoice];
			  // here we should update pcHeap with the constraint attr == candidateNode.sym_v
			  pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, candidateNode.getSymbolic());
	          daIndex = candidateNode.getIndex();
		}
		else if (currentChoice == numSymRefs) { //existing (null)
			pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, new IntegerConstant(-1));
			daIndex = MJIEnv.NULL;
		} else if (currentChoice == (numSymRefs + 1) && !abstractClass) {
			  // creates a new object with all fields symbolic and adds the object to SymbolicHeap
			  daIndex = Helper.addNewHeapNode(typeClassInfo, ti, attr, pcHeap,
					  		symInputHeap, numSymRefs, prevSymRefs, ei.isShared());
		  } else {
			  //TODO: fix
			  System.err.println("subtyping not handled");
		  }


		ei.setReferenceField(fi,daIndex );
		ei.setFieldAttr(fi, null);//Helper.SymbolicNull); // was null
		StackFrame frame = ti.getModifiableTopFrame();
		frame.pushRef(daIndex);
		((HeapChoiceGenerator)heapCG).setCurrentPCheap(pcHeap);
		((HeapChoiceGenerator)heapCG).setCurrentSymInputHeap(symInputHeap);
		if (SymbolicInstructionFactory.debugMode)
			System.out.println("GETSTATIC pcHeap: " + pcHeap);
		return getNext(ti);

	}


}


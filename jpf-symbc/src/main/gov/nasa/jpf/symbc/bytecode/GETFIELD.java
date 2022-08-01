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
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.StackFrame;
//import gov.nasa.jpf.symbc.uberlazy.TypeHierarchy;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.choice.IntChoiceFromSet;

public class GETFIELD extends gov.nasa.jpf.jvm.bytecode.GETFIELD {
	public GETFIELD(String fieldName, String clsName, String fieldDescriptor){
	    super(fieldName, clsName, fieldDescriptor);
	  }
	
  // private int numNewRefs = 0; // # of new reference objects to account for polymorphism -- work of Neha Rungta -- needs to be updated
	
	boolean abstractClass = false;


  @Override
  public Instruction execute (ThreadInfo ti) {
	  
	  HeapNode[] prevSymRefs = null; // previously initialized objects of same type: candidates for lazy init
	  int numSymRefs = 0; // # of prev. initialized objects
	  ChoiceGenerator<?> prevHeapCG = null;

	  Config conf = ti.getVM().getConfig();
	  String[] lazy = conf.getStringArray("symbolic.lazy");
	  if (lazy == null || !lazy[0].equalsIgnoreCase("true")){
		  return super.execute(ti);
	  }

	  

	    StackFrame frame = ti.getModifiableTopFrame();
	    int objRef = frame.peek(); // don't pop yet, we might re-enter
	    lastThis = objRef;
	    if (objRef == MJIEnv.NULL) {
	      return ti.createAndThrowException("java.lang.NullPointerException",
	                                        "referencing field '" + fname + "' on null object");
	    }

	    
	    ElementInfo ei = ti.getModifiableElementInfo(objRef); //getModifiableElementInfoWithUpdatedSharedness(objRef); POR broken
	    FieldInfo fi = getFieldInfo();
	    if (fi == null) {
	      return ti.createAndThrowException("java.lang.NoSuchFieldError",
	                                        "referencing field '" + fname + "' in " + ei);
	    }
	    
	 Object attr = ei.getFieldAttr(fi);
	  // check if the field is of ref type & it is symbolic (i.e. it has an attribute)
	  // if it is we need to do lazy initialization

	  if (!(fi.isReference() && attr != null)) {
		  return super.execute(ti);
	  }

	  if(attr instanceof StringExpression || attr instanceof SymbolicStringBuilder)
			return super.execute(ti); // Strings are handled specially

	  if (SymbolicInstructionFactory.debugMode)
		  System.out.println("lazy initialization");
	  // else: lazy initialization

	  // POR broken again
	// check if this breaks the current transition//
	// may introduce thread choice
	//    if (isNewPorFieldBoundary(ti, fi, objRef)) {
	//      if (createAndSetSharedFieldAccessCG( ei, ti)) {
	      //  return this; 
	//      }
	 //   }
	  
	  int currentChoice;
	  ChoiceGenerator<?> thisHeapCG;
	  
	  ClassInfo typeClassInfo = fi.getTypeClassInfo(); // use this instead of fullType

	 
	  if(!ti.isFirstStepInsn()){
          prevSymRefs = null;
		  numSymRefs = 0;
		  
		  prevHeapCG = ti.getVM().getSystemState().getLastChoiceGeneratorOfType(HeapChoiceGenerator.class);
		  // to check if this still works in the case of cascaded choices...

		  if (prevHeapCG != null) {
			// determine # of candidates for lazy initialization
			  SymbolicInputHeap symInputHeap =
				  ((HeapChoiceGenerator)prevHeapCG).getCurrentSymInputHeap();
			  prevSymRefs = symInputHeap.getNodesOfType(typeClassInfo);
			  numSymRefs = prevSymRefs.length;
		  }
		  int increment = 2;
		  if(typeClassInfo.isAbstract()) {
			  abstractClass = true;
			  increment = 1; // only null
		  }

		  thisHeapCG = new HeapChoiceGenerator(numSymRefs+increment);  //+null,new
		  ti.getVM().getSystemState().setNextChoiceGenerator(thisHeapCG);
          //ti.reExecuteInstruction();
		  if (SymbolicInstructionFactory.debugMode)
			  System.out.println("# heap cg registered: " + thisHeapCG);
          return this;

      } else { //this is what really returns results
		 // here we can have 2 choice generators: thread and heappc at the same time?
		  
		
		  frame.pop(); // Ok, now we can remove the object ref from the stack

		  thisHeapCG = ti.getVM().getSystemState().getLastChoiceGeneratorOfType(HeapChoiceGenerator.class);
		  assert (thisHeapCG !=null && thisHeapCG instanceof HeapChoiceGenerator) :
			  "expected HeapChoiceGenerator, got: " + thisHeapCG;
		  currentChoice = ((HeapChoiceGenerator) thisHeapCG).getNextChoice();
	  }

	  PathCondition pcHeap; //this pc contains only the constraints on the heap
	  SymbolicInputHeap symInputHeap;

	  // depending on the currentChoice, we set the current field to an object that was already created
	  // 0 .. numymRefs -1, or to null or to a new object of the respective type, where we set all its
	  // fields to be symbolic

	  prevHeapCG = thisHeapCG.getPreviousChoiceGeneratorOfType(HeapChoiceGenerator.class);
	  
	  
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
	  if (currentChoice < numSymRefs) { // lazy initialization using a previously lazily initialized object
		  HeapNode candidateNode = prevSymRefs[currentChoice];
		  // here we should update pcHeap with the constraint attr == candidateNode.sym_v
		  pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, candidateNode.getSymbolic());
          daIndex = candidateNode.getIndex();
	  }
	  else if (currentChoice == numSymRefs){ //null object
		  pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, new IntegerConstant(-1));
		  daIndex = MJIEnv.NULL;//-1;
	  }
	  else if (currentChoice == (numSymRefs + 1) && !abstractClass) {
		  // creates a new object with all fields symbolic and adds the object to SymbolicHeap
		  
		  daIndex = Helper.addNewHeapNode(typeClassInfo, ti, attr, pcHeap,
				  		symInputHeap, numSymRefs, prevSymRefs, ei.isShared());
	  } else {
		  System.err.println("subtyping not handled");
	  }

	  
	 ei.setReferenceField(fi,daIndex );
	 ei.setFieldAttr(fi, null);

	  frame.pushRef(daIndex);
      
	  ((HeapChoiceGenerator)thisHeapCG).setCurrentPCheap(pcHeap);
	  ((HeapChoiceGenerator)thisHeapCG).setCurrentSymInputHeap(symInputHeap);
	  if (SymbolicInstructionFactory.debugMode)
		  System.out.println("GETFIELD pcHeap: " + pcHeap);
	  return getNext(ti);
  }


}

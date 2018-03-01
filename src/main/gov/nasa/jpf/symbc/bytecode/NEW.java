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

import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.Heap;
import gov.nasa.jpf.vm.LoadOnJPFRequired;

import gov.nasa.jpf.vm.ThreadInfo;

import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.symbc.string.SymbolicStringBuilder;


// Corina's comment: probably this is not necessary here

// TODO: to review

import gov.nasa.jpf.vm.Instruction;

/**
 * Create new object
 * ... => ..., objectref
 */
public class NEW extends gov.nasa.jpf.jvm.bytecode.NEW {
	public NEW (String clsName) {
	    super(clsName);
	  }
  @Override
  public Instruction execute (ThreadInfo ti) {
	  Heap heap = ti.getHeap();
	    ClassInfo ci;

	    // resolve the referenced class
	    ClassInfo cls = ti.getTopFrameMethodInfo().getClassInfo();
	    try {
	      ci = cls.resolveReferencedClass(cname);
	    } catch(LoadOnJPFRequired lre) {
	      return ti.getPC();
	    }

	    String className = ci.getName();
	      if(!(className.equals("java.lang.StringBuilder") || className.equals("java.lang.StringBuffer")))
	    	  return super.execute(ti);
	    
	    if (!ci.isRegistered()){
	      ci.registerClass(ti);
	    }

	    // since this is a NEW, we also have to pushClinit
	    if (!ci.isInitialized()) {
	      if (ci.initializeClass(ti)) {
	        return ti.getPC();  // reexecute this instruction once we return from the clinits
	      }
	    }

	    if (heap.isOutOfMemory()) { // simulate OutOfMemoryError
	      return ti.createAndThrowException("java.lang.OutOfMemoryError",
	                                        "trying to allocate new " + cname);
	    }

	    ElementInfo ei = heap.newObject(ci, ti);
	    int objRef = ei.getObjectRef();
	    newObjRef = objRef;

	    // pushes the return value onto the stack
	    StackFrame frame = ti.getModifiableTopFrame();
	    frame.pushRef( objRef);

	 // TODO: to review
	    //insert dummy expressions for StringBuilder and StringBuffer
	    //String className = ci.getName();
	    if(className.equals("java.lang.StringBuilder") || className.equals("java.lang.StringBuffer")){
	    	SymbolicStringBuilder t = new SymbolicStringBuilder();
	    	StackFrame sf = ti.getModifiableTopFrame();
	    	sf.setOperandAttr(t);
	    }
	    
	    return getNext(ti);

  }

}
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

//
// Copyright (C) 2007 United States Government as represented by the
// Administrator of the National Aeronautics and Space Administration
// (NASA).  All Rights Reserved.
//
// This software is distributed under the NASA Open Source Agreement
// (NOSA), version 1.3.  The NOSA has been approved by the Open Source
// Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
// directory tree for the complete NOSA document.
//
// THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
// KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
// LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
// SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
// THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
// DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//
package gov.nasa.jpf.symbc.heap;


import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.choice.IntIntervalGenerator;


public class HeapChoiceGenerator extends IntIntervalGenerator {

	protected PathCondition [] PCheap; // maintains constraints on the heap: one PC per choice
    protected SymbolicInputHeap [] symInputHeap; // maintains list of input symbolic nodes; one list per choice

	@SuppressWarnings("deprecation")
	public HeapChoiceGenerator(int size) {
		super(0, size - 1);
		PCheap = new PathCondition[size];
		symInputHeap = new SymbolicInputHeap[size];
	}

	// sets the heap constraints for the current choice
	public void setCurrentPCheap(PathCondition pc) {
		PCheap[getNextChoice()] = pc;

	}

	// returns the heap constraints for the current choice
	public PathCondition getCurrentPCheap() {
		PathCondition pc;

		pc = PCheap[getNextChoice()];
		if (pc != null) {
			return pc.make_copy();
		} else {
			return null;
		}
	}

    // sets the heap constraints for the current choice
	public void setCurrentSymInputHeap(SymbolicInputHeap ih) {
		symInputHeap[getNextChoice()] = ih;

	}

	// returns the heap constraints for the current choice
	public SymbolicInputHeap getCurrentSymInputHeap() {
		SymbolicInputHeap ih;

		ih = symInputHeap[getNextChoice()];
		if (ih != null) {
			return ih.make_copy();
		} else {
			return null;
		}
	}


}

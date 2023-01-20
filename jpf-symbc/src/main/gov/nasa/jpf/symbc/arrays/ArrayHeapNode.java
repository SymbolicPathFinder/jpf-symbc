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

package gov.nasa.jpf.symbc.arrays;

import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.vm.ClassInfo;

public class ArrayHeapNode extends HeapNode {
    // Used to store the index this object was previously loaded from
    public IntegerExpression arrayIndex = null;
    public int arrayRef = -1;

        public ArrayHeapNode(int idx, ClassInfo tClassInfo, SymbolicInteger sym, IntegerExpression index, int ref) {
            super(idx, tClassInfo, sym);
            arrayIndex = index;
            arrayRef = ref;
        }
}

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

import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;


/**
 * Subtract float
 * ..., value1, value2 => ..., result
 */
public class FSUB extends gov.nasa.jpf.jvm.bytecode.FSUB {

  @Override
  public Instruction execute (ThreadInfo th) {
	  
	StackFrame sf = th.getModifiableTopFrame();
	
	RealExpression sym_v1 = (RealExpression) sf.getOperandAttr();
	float v1 = sf.popFloat();
	RealExpression sym_v2 = (RealExpression) sf.getOperandAttr();
	float v2 = sf.popFloat();
    
    float r = v2 - v1;
    sf.push(Types.floatToInt(r), false); 
    
    RealExpression result = null;
	if(sym_v2!=null) {
		if (sym_v1!=null)
			result = sym_v2._minus(sym_v1);
		else // v1 is concrete
			result = sym_v2._minus(v1);
	}else if (sym_v1!=null)
		result = sym_v1._minus_reverse(v2);
	
	sf.setOperandAttr(result);


    return getNext(th);
  }

}

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


import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;


/**
 * Subtract long
 * ..., value1, value2 => ..., result
 */
public class LSUB extends gov.nasa.jpf.jvm.bytecode.LSUB {

  @Override
  public Instruction execute (ThreadInfo th) {
	  	StackFrame sf = th.getModifiableTopFrame();
	  
		IntegerExpression sym_v1 = (IntegerExpression) sf.getOperandAttr(1);
		IntegerExpression sym_v2 = (IntegerExpression) sf.getOperandAttr(3);
	    
	    if(sym_v1==null && sym_v2==null)
	        return super.execute(th);// we'll still do the concrete execution
	    else {
	    	long v1 = sf.popLong();
	    	long v2 = sf.popLong();
	    	sf.pushLong(v2 - v1);

	    	IntegerExpression result = null;
	    	if(sym_v2!=null) {
	    		if (sym_v1!=null)
	    			result = sym_v2._minus(sym_v1);
	    		else // v1 is concrete
	    			result = sym_v2._minus(v1);
	    	}
	    	else if (sym_v1!=null)
	    		result = sym_v1._minus_reverse(v2);

	    	sf.setLongOperandAttr(result);

	    	//System.out.println("Execute LSUB: "+result);

	    	return getNext(th);
	    }
  }
}

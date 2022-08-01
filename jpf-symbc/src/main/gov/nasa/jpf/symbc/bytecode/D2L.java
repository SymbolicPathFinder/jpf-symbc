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




import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;



/**
 * Convert double to long
 * ..., value => ..., result
 */
public class D2L extends gov.nasa.jpf.jvm.bytecode.D2L {

  @Override
  public Instruction execute (ThreadInfo th) {
	  RealExpression sym_dval = (RealExpression) th.getModifiableTopFrame().getLongOperandAttr();
		
	  if(sym_dval == null) {
		  return super.execute(th); 
	  }
	  else {
		  //throw new RuntimeException("## Error: symbolic D2L not yet hanled ");

		  //System.out.println("Execute symbolic D2L");
		 
		  // here we get a hold of the current path condition and 
		  // add an extra mixed constraint sym_dval==sym_ival

		    ChoiceGenerator cg; 
			if (!th.isFirstStepInsn()) { // first time around
				cg = new PCChoiceGenerator(1); // only one choice 
				th.getVM().getSystemState().setNextChoiceGenerator(cg);
				return this;  	      
			} else {  // this is what really returns results
				cg = th.getVM().getSystemState().getChoiceGenerator();
				assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
			}	
			
			// get the path condition from the 
			// previous choice generator of the same type 

		    PathCondition pc;
			ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);

			if (prev_cg == null)
				pc = new PathCondition(); // TODO: handling of preconditions needs to be changed
			else 
				pc = ((PCChoiceGenerator)prev_cg).getCurrentPC();
			assert pc != null;
			
			StackFrame sf = th.getModifiableTopFrame();
			
		    double v = sf.popDouble();
		    sf.pushLong( (long) v);
		    
		    SymbolicInteger sym_ival = new SymbolicInteger();
			sf.setLongOperandAttr(sym_ival);
			
			pc._addDet(Comparator.EQ, sym_dval, sym_ival);
			
			if(!pc.simplify())  { // not satisfiable
				th.getVM().getSystemState().setIgnored(true);
			} else {
				//pc.solve();
				((PCChoiceGenerator) cg).setCurrentPC(pc);
				//System.out.println(((PCChoiceGenerator) cg).getCurrentPC());
			}
			
			//System.out.println("Execute D2L: " + sf.getLongOperandAttr());
			return getNext(th);
	  }
  }
}

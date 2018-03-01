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





import gov.nasa.jpf.vm.Verify;

import java.util.EnumSet;

public class ExampleAbort {
	enum Failure { EARTH_SENSOR, LAS_CNTRL, CM_MASS, CM_RCS };
	EnumSet<Failure> failures = EnumSet.noneOf(Failure.class); 
	
	boolean nextStateSelected = false;  
	
	public static void main(String[] args) {
		int alt = 0; // this value is ignored if we want to execute the method symbolically
		boolean ctrlMotorField = Verify.randomBool(); 
		System.out.println("Invoke abort with ctrlMotorField="+ctrlMotorField);
		(new ExampleAbort()).abort(alt,ctrlMotorField);
	}

	// this is a simplified example showing method abort taken from CEV_15EOR_LOR
    public void abort (int altitude, boolean controlMotorFired) {
      if (!controlMotorFired) 
    	  failures.add(Failure.LAS_CNTRL);
      
      if (altitude <= 120000) {
        if (controlMotorFired) {
          setNextState("abortLowActiveLAS");
        } else {
          setNextState("abortPassiveLAS");
        }
      }
      
      if (altitude >= 120000) { 
    	  setNextState("abortHighActiveLAS");
      }
      
    }
    
    public void setNextState (String nextState) {
    	assert !nextStateSelected : "ambiguous transition";
    	nextStateSelected = true;
    	System.out.println("next state is:" + nextState);
    }
    
    
}

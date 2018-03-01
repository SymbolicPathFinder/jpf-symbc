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

package gov.nasa.jpf.symbc.numeric.solvers;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;

public class IncrementalListener extends PropertyListenerAdapter {
  
  private IncrementalSolver solver;
  
  public IncrementalListener(Config config, JPF jpf) {
    String stringDp = SymbolicInstructionFactory.dp[0];
    if(stringDp.equalsIgnoreCase("z3inc")){
      solver = new ProblemZ3Incremental();
    }  else if(stringDp.equalsIgnoreCase("z3bitvectorinc")){
      solver = new ProblemZ3BitVectorIncremental();
    } else {
      System.err.println("Trying to use incremental listener, but solver " + stringDp + " does not support incremental solving (try z3inc or z3bitvectorinc)");
      jpf.removeListener(this);
    }

  }
  @Override
  public void stateBacktracked(Search search) {
    if(search.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
      solver.pop();
    }
  }
}

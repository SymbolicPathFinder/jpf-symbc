/*
 * Copyright (C) 2015, United States Government, as represented by the
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
package gov.nasa.jpf.symbc.tree;

import gov.nasa.jpf.jvm.bytecode.DIRECTCALLRETURN;
import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.bytecode.InvokeInstruction;
import gov.nasa.jpf.vm.bytecode.ReturnInstruction;

/**
 * @author Kasper Luckow
 */
public interface Filter {
  
  // These implementations can be used with
  // symbolic.tree.filter
  public static class AllInstrFilter implements Filter {
    @Override
    public boolean apply(Instruction executedInstruction, Instruction instrToBeExecuted, VM vm, ThreadInfo currentThread) {
      return true;
    }
  }
  
  public static class SymbolicDecisionFilter implements Filter {
    @Override
    public boolean apply(Instruction executedInstruction, Instruction instrToBeExecuted, VM vm, ThreadInfo currentThread) {
      PCChoiceGenerator pc = vm.getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
      if(pc != null)
        return (pc.getInsn() == executedInstruction);
      return false;
    }
  }
  
  public static class ConstInstrFilter implements Filter {
    @Override
    public boolean apply(Instruction executedInstruction, Instruction instrToBeExecuted, VM vm, ThreadInfo currentThread) {
      return (instrToBeExecuted instanceof IfInstruction || 
          instrToBeExecuted instanceof ReturnInstruction);
    }
  }
  
  public static class InvokeInstrFilter implements Filter {
    @Override
    public boolean apply(Instruction executedInstruction, Instruction instrToBeExecuted, VM vm, ThreadInfo currentThread) {
      return instrToBeExecuted instanceof InvokeInstruction;
    }
  }
  
  public boolean apply(Instruction executedInstruction, Instruction instrToBeExecuted, VM vm, ThreadInfo currentThread);
  
}

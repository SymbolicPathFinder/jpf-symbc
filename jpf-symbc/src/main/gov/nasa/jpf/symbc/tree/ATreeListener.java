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

import java.util.HashMap;
import java.util.Map;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

/**
 * @author Kasper Luckow
 * TODO: There might be issues with non-determinism
 */
public abstract class ATreeListener<T> extends PropertyListenerAdapter {

  protected final Config jpfConf;
  private boolean symbolicMethodStarted;
  protected final NodeFactory<T> nodeFactory;
  protected Map<Integer, T> nodeMap = new HashMap<>();
  protected T prev;
  protected Instruction executed;
  
  private final static String FILTER = "symbolic.tree.filter";
  protected Filter nodePredicate;
  
  public ATreeListener(Config conf, JPF jpf) {
    this.symbolicMethodStarted = false;
    this.jpfConf = conf;
    this.nodeFactory = getNodeFactory();
    this.nodePredicate = (conf.hasValue(FILTER)) ? conf.getInstance(FILTER, Filter.class) : new Filter.AllInstrFilter();
    this.prev = null;
  }

  protected abstract NodeFactory<T> getNodeFactory();
  
  protected void processTree() { }

  private boolean isSymbolic(Config jpfConf, MethodInfo method) {
    return BytecodeUtils.isClassSymbolic(jpfConf, method.getClassInfo().getName(), method, method.getBaseName())
        || BytecodeUtils.isMethodSymbolic(jpfConf, method.getFullName(), method.getNumberOfArguments(), null);
  }

  @Override
  public void methodEntered (VM vm, ThreadInfo currentThread, MethodInfo enteredMethod) {
    if(!this.symbolicMethodStarted)
      this.symbolicMethodStarted = isSymbolic(this.jpfConf, enteredMethod);
  }

  protected boolean isRelevantState(VM vm, ThreadInfo thread) {
    return !vm.getSystemState().isIgnored() && 
           this.symbolicMethodStarted && 
           !thread.isFirstStepInsn();
  }
  
  @Override
  public void executeInstruction(VM vm, ThreadInfo currentThread, Instruction instructionToExecute) {
    if(isRelevantState(vm, currentThread)) {
      if(nodePredicate.apply(executed, instructionToExecute, vm, currentThread)) {
        T node = this.nodeFactory.constructNode(prev, instructionToExecute, vm);
        this.prev = node; 
      }
    }
    executed = instructionToExecute;
  }

  @Override
  public void searchFinished(Search search) {
    processTree();
  }

  @Override
  public void choiceGeneratorAdvanced (VM vm, ChoiceGenerator<?> currentCG) {
    if(!vm.getSystemState().isIgnored() && this.symbolicMethodStarted) {
      if(vm.getSearch().isNewState()) {
        this.nodeMap.put(vm.getSearch().getStateId(), this.prev);
      }
    }
  }
  
  @Override
  public void stateBacktracked(Search search) {
    if(!search.getVM().getSystemState().isIgnored() && this.symbolicMethodStarted) {
      this.prev = this.nodeMap.get(search.getStateId());
    }
  }
}

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

package gov.nasa.jpf.symbc;

import java.util.Map;
import java.util.concurrent.BlockingQueue;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.concolic.PCAnalyzer;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.util.Pair;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

public class SymbolicListener2 extends PropertyListenerAdapter {

    BlockingQueue<Pair<PathCondition, Map<String, Object>>> pcAndSolutionQueue;

    private String targetMethodName;

    public SymbolicListener2(Config conf, JPF jpf, BlockingQueue<Pair<PathCondition, Map<String, Object>>> pcAndSolutionQueue) {
        targetMethodName = conf.getProperty("symbolic.method").substring(0, conf.getProperty("symbolic.method").indexOf("("));
        this.pcAndSolutionQueue = pcAndSolutionQueue;
    }

    @Override
    public void methodExited(VM vm, ThreadInfo currentThread, MethodInfo exitedMethod) {
        String currentMethod = exitedMethod.getFullName().substring(0, exitedMethod.getFullName().indexOf("("));
        if (currentMethod.equals(targetMethodName)) {
            ChoiceGenerator<?> cg = vm.getChoiceGenerator();
            if (!(cg instanceof PCChoiceGenerator)) {
                ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
                while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
                    prev_cg = prev_cg.getPreviousChoiceGenerator();
                }
                cg = prev_cg;
            }
            if ((cg instanceof PCChoiceGenerator) && ((PCChoiceGenerator) cg).getCurrentPC() != null) {
                PathCondition pc = ((PCChoiceGenerator) cg).getCurrentPC();
                handleNewPathCondition(pc);
            }
        }
    }

    @Override
    public void propertyViolated(Search search) {

        VM vm = search.getVM();

        ChoiceGenerator<?> cg = vm.getChoiceGenerator();
        if (!(cg instanceof PCChoiceGenerator)) {
            ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
            while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
                prev_cg = prev_cg.getPreviousChoiceGenerator();
            }
            cg = prev_cg;
        }
        if ((cg instanceof PCChoiceGenerator) && ((PCChoiceGenerator) cg).getCurrentPC() != null) {
            PathCondition pc = ((PCChoiceGenerator) cg).getCurrentPC();
            handleNewPathCondition(pc);
        }
    }
    
    private void handleNewPathCondition(PathCondition pc) {
        boolean sat;
        if (SymbolicInstructionFactory.concolicMode) { // TODO: cleaner
            SymbolicConstraintsGeneral solver = new SymbolicConstraintsGeneral();
            PCAnalyzer pa = new PCAnalyzer();
            sat = pa.solve(pc, solver);
        } else
            sat = pc.solve();
        
        Map<String, Object> solution = null;
        if (sat) {
            solution = pc.solveWithValuation();
        }
        if (solution != null) {
            try {
                pcAndSolutionQueue.put(new Pair<>(pc, solution));
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
    }
}

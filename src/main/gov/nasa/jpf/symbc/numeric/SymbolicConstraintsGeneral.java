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
//Copyright (C) 2005 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.
//
//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.
//
//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

package gov.nasa.jpf.symbc.numeric;

import gov.nasa.jpf.symbc.Observations;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.solvers.*;
import gov.nasa.jpf.symbc.numeric.visitors.ProblemGeneralVisitor;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

// generalized to use different constraint solvers/decision procedures
// Warning: should never use / modify the types from pb:
// types come in and out of each particular dp !!!!!!!!!!!!!!!

public class SymbolicConstraintsGeneral {
    protected ProblemGeneral pb;
    protected Boolean result; // tells whether result is satisfiable or not

    public boolean isSatisfiable(PathCondition pc) {
        if (pc == null || pc.count == 0) {
            if (SymbolicInstructionFactory.debugMode)
                System.out.println("## Warning: empty path condition");
            return true;
        }

        if (pc.count() > SymbolicInstructionFactory.maxPcLength) {
            System.out.println("## Warning: Path condition exceeds symbolic.max_pc_length="
                    + SymbolicInstructionFactory.maxPcLength + ".  Pretending it is unsatisfiable.");
            return false;
        }
        if (SymbolicInstructionFactory.maxPcMSec > 0 && System.currentTimeMillis()
                - SymbolicInstructionFactory.startSystemMillis > SymbolicInstructionFactory.maxPcMSec) {
            System.out.println("## Warning: Exploration time exceeds symbolic.max_pc_msec="
                    + SymbolicInstructionFactory.maxPcMSec + ".  Pretending all paths are unsatisfiable.");
            return false;
        }

        // if (SymbolicInstructionFactory.debugMode)
        // System.out.println("checking: PC "+pc);

        String[] dp = SymbolicInstructionFactory.dp;
        if (dp == null) { // default: use choco
            pb = new ProblemChoco();
        } else if (dp[0].equalsIgnoreCase("choco")) {
            pb = new ProblemChoco();
            // } else if(dp[0].equalsIgnoreCase("choco2")){
            // pb = new ProblemChoco2();
        } else if (dp[0].equalsIgnoreCase("coral")) {
            pb = new ProblemCoral();
        } else if (dp[0].equalsIgnoreCase("iasolver")) {
            pb = new ProblemIAsolver();
        } else if (dp[0].equalsIgnoreCase("cvc3")) {
            pb = new ProblemCVC3();
        } else if (dp[0].equalsIgnoreCase("cvc3bitvec")) {
            pb = new ProblemCVC3BitVector();
        } else if (dp[0].equalsIgnoreCase("yices")) {
            pb = new ProblemYices();
        } else if (dp[0].equalsIgnoreCase("z3")) {
            pb = new ProblemZ3();
        } else if (dp[0].equalsIgnoreCase("z3inc")) {
            pb = new ProblemZ3Incremental();
        } else if (dp[0].equalsIgnoreCase("z3bitvectorinc")) {
            pb = new ProblemZ3BitVectorIncremental();
        } else if (dp[0].equalsIgnoreCase("debug")) {
            pb = new DebugSolvers(pc);
        } else if (dp[0].equalsIgnoreCase("compare")) {
            pb = new ProblemCompare(pc, this);
        } else if (dp[0].equalsIgnoreCase("z3bitvector")) {
            pb = new ProblemZ3BitVector();
        } else if (dp[0].equalsIgnoreCase("z3optimize")) {
            pb = new ProblemZ3Optimize();
        }
        // added option to have no-solving
        // as a result symbolic execution will explore an over-approximation of the
        // program paths
        // equivalent to a CFG analysis
        else if (dp[0].equalsIgnoreCase("no_solver")) {
            return true;
        } else
            throw new RuntimeException(
                    "## Error: unknown decision procedure symbolic.dp=" + dp[0] + "\n(use choco or IAsolver or CVC3)");

        /*
         * Parse path condition to solver. Note: do not override the actual pb
         * variable in case the result is null. The cleanup afterwards will not
         * work otherwise and the solver gets filled up with wrong assertions,
         * e.g. with Z3.
         */
        ProblemGeneral tempPb = PCParser.parse(pc, pb);

        if (tempPb == null)
            result = Boolean.FALSE;
        else {
            pb = tempPb;

            // YN: z3 optimize
            if (Observations.lastObservedSymbolicExpression != null) {
                if (pb instanceof ProblemZ3Optimize) {
                    ((ProblemZ3Optimize) pb).maximize(
                            PCParser.getExpression((IntegerExpression) Observations.lastObservedSymbolicExpression));
                }
            }
            result = pb.solve();
            //System.out.println("numeric PC: " + pc + " -> " + result + "\n");
        }

        if (SymbolicInstructionFactory.debugMode)
            System.out.println("numeric PC: " + pc + " -> " + result + "\n");

        if (SymbolicInstructionFactory.regressMode) {
            String output = "##NUMERIC PC: ";
            output = output + (result == Boolean.TRUE ? "(SOLVED)" : "(UNSOLVED)");
            output = output + " " + pc;
            System.out.println(output);
        }

        if (result == null) {
            return false;
        }
        if (result == Boolean.TRUE) {
            return true;
        } else {
            return false;
        }

    }

    public boolean isSatisfiableGreen(PathCondition pc) {
        if (pc == null || pc.count == 0) {
            if (SymbolicInstructionFactory.debugMode)
                System.out.println("## Warning: empty path condition");
            return true;
        }
        result = pc.solve();

        if (SymbolicInstructionFactory.debugMode)
            System.out.println(" --> " + pc + " -> " + result);

        if (result == null) {
            return false;
        }
        if (result == Boolean.TRUE) {
            return true;
        } else {
            return false;
        }

    }

    public void cleanup() {
        if (pb instanceof ProblemCVC3) {
            ((ProblemCVC3) pb).cleanup();
        } else if (pb instanceof ProblemCoral) {
            ((ProblemCoral) pb).cleanup();
        } else if (pb instanceof ProblemZ3) {
            ((ProblemZ3) pb).cleanup();
        } else if (pb instanceof ProblemZ3BitVector) {
            ((ProblemZ3BitVector) pb).cleanup();
        } else if (pb instanceof ProblemZ3Optimize) {
            ((ProblemZ3Optimize) pb).cleanup();
        }
    }

    public boolean solve(PathCondition pc) {
    	
        // if (SymbolicInstructionFactory.debugMode)
        // System.out.println("solving: PC " + pc);

        if (pc == null || pc.count == 0)
            return true;

        String[] dp = SymbolicInstructionFactory.dp;
        if (dp[0].equalsIgnoreCase("no_solver"))
            return true;
        if (isSatisfiable(pc)) {

            // compute solutions for real variables:
        	
        	Set<Entry<SymbolicReal, Object>> sym_realvar_mappings = PCParser.symRealVar.entrySet();
        	
            Iterator<Entry<SymbolicReal, Object>> i_real = sym_realvar_mappings.iterator();
            // first set inf / sup values
            // while(i_real.hasNext()) {
            // Entry<SymbolicReal,Object> e = i_real.next();
            // SymbolicReal pcVar = e.getKey();
            // Object dpVar = e.getValue();
            // pcVar.solution_inf=pb.getRealValueInf(dpVar);
            // pcVar.solution_sup=pb.getRealValueSup(dpVar);
            // }

            try {
                sym_realvar_mappings = PCParser.symRealVar.entrySet();
                i_real = sym_realvar_mappings.iterator();
                while (i_real.hasNext()) {
                    Entry<SymbolicReal, Object> e = i_real.next();
                    SymbolicReal pcVar = e.getKey();
                    Object dpVar = e.getValue();
                    pcVar.solution = pb.getRealValue(dpVar); // may be undefined: throws an exception
                }
            } catch (Exception exp) {
            	this.catchBody(PCParser.symRealVar, pb, pc);
            } // end catch

            // compute solutions for integer variables
            
            Set<Entry<SymbolicInteger, Object>> sym_intvar_mappings = PCParser.symIntegerVar.entrySet();
            Iterator<Entry<SymbolicInteger, Object>> i_int = sym_intvar_mappings.iterator();
            // try {
            while (i_int.hasNext()) {
                Entry<SymbolicInteger, Object> e = i_int.next();
                e.getKey().solution = pb.getIntValue(e.getValue());

            }
            // }
            /*
             * catch (Exception exp) { Boolean isSolvable = true; sym_intvar_mappings = symIntegerVar.entrySet(); i_int
             * = sym_intvar_mappings.iterator();
             *
             * while(i_int.hasNext() && isSolvable) { Entry<SymbolicInteger,Object> e = i_int.next(); SymbolicInteger
             * pcVar = e.getKey(); Object dpVar = e.getValue(); // cast pcVar.solution=(int)(pb.getRealValueInf(dpVar) +
             * pb.getRealValueSup(dpVar)) / 2; //(int)pcVar.solution_inf;
             *
             * pb.post(pb.eq(dpVar, pcVar.solution)); isSolvable = pb.solve(); if (isSolvable == null) isSolvable =
             * Boolean.FALSE; } if(!isSolvable) System.err.println("# Warning: PC "+pc.stringPC()
             * +" is solvable but could not find the solution!"); } // end catch
             */
            cleanup();
            return true;
        } else
            return false;
    }

    /**
     * The "ProblemCompare" solver calls this to deal with yices and choco refinements of solution ranges.
     */
    public Map<SymbolicReal, Object> catchBody(Map<SymbolicReal, Object> realVars, ProblemGeneral prob,
            PathCondition pc) {
        Set<Entry<SymbolicReal, Object>> sym_realvar_mappings;
        Iterator<Entry<SymbolicReal, Object>> i_real;

        // For each variable Xi:
        // Choose a value Vi for Xi from its range
        // Add "Xi == Vi" to the Choco problem
        // Solve the problem to get new ranges of values for the remaining
        // variables.

        Boolean isSolvable = true;
        sym_realvar_mappings = realVars.entrySet();
        i_real = sym_realvar_mappings.iterator();

        while (i_real.hasNext() && isSolvable) {
            Entry<SymbolicReal, Object> e = i_real.next();
            SymbolicReal pcVar = e.getKey();
            Object dpVar = e.getValue();

            // Note: using solution_inf or solution_sup alone sometimes fails
            // because of floating point inaccuracies
            // trick to get a better value: cast to float?
            pcVar.solution = prob.getRealValueInf(dpVar);
            // (prob.getRealValueInf(dpVar) + prob
            // .getRealValueSup(dpVar)) / 2;
            // (float)pcVar.solution_inf;
            // prob.post(prob.eq(dpVar, pcVar.solution));
            // isSolvable = prob.solve();
            // if (isSolvable == null)
            // isSolvable = Boolean.FALSE;

        }
        if (!isSolvable) {
            System.out.println("# Warning: PC " // + pc.stringPC()
                    + " is solvable but could not find the solution!");
            return null; // alert debugSolver to not bother checking this result
        } else {
            return realVars;
        }

    }

    public Map<String, Object> solveWithValuation(PathCondition pc) {
        Map<String, Object> result = new HashMap<String, Object>();

        if (pc == null || pc.count == 0) {
            return result;
        }

        String[] dp = SymbolicInstructionFactory.dp;
        if (dp[0].equalsIgnoreCase("no_solver")) {
            return result;
        }

        if (isSatisfiable(pc)) {

            // compute solutions for real variables:
            Set<Entry<SymbolicReal, Object>> sym_realvar_mappings = PCParser.symRealVar.entrySet();
            Iterator<Entry<SymbolicReal, Object>> i_real = sym_realvar_mappings.iterator();

            try {
                sym_realvar_mappings = PCParser.symRealVar.entrySet();
                i_real = sym_realvar_mappings.iterator();
                while (i_real.hasNext()) {
                    Entry<SymbolicReal, Object> e = i_real.next();
                    SymbolicReal pcVar = e.getKey();
                    Object dpVar = e.getValue();
                    double e_value = pb.getRealValue(dpVar); // may be undefined: throws an exception
                    pcVar.solution = e_value; 
                    result.put(pcVar.getName(), e_value);
                }
            } catch (Exception exp) {
                this.catchBody(PCParser.symRealVar, pb, pc);
            }

            // compute solutions for integer variables
            Set<Entry<SymbolicInteger, Object>> sym_intvar_mappings = PCParser.symIntegerVar.entrySet();
            Iterator<Entry<SymbolicInteger, Object>> i_int = sym_intvar_mappings.iterator();
            // try {
            while (i_int.hasNext()) {
                Entry<SymbolicInteger, Object> e = i_int.next();
                long e_value = pb.getIntValue(e.getValue());
                e.getKey().solution = e_value;
                result.put(e.getKey().getName(), e_value);

            }
            cleanup();
            return result;
        } else {
            return result;
        }
    }

}

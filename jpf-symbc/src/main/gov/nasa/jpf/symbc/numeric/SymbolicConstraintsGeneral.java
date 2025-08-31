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

import edu.ucsb.cs.vlab.Z3;
import gov.nasa.jpf.symbc.Observations;
import gov.nasa.jpf.symbc.SPFException;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.solvers.*;
import javafx.util.Pair;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;
import java.util.List;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;


// generalized to use different constraint solvers/decision procedures
// Warning: should never use / modify the types from pb:
// types come in and out of each particular dp !!!!!!!!!!!!!!!

public class SymbolicConstraintsGeneral {
    /**
     * List of all solvers that will be used to try solving a path condition.
     */
    protected List<ProblemGeneral> solvers;
    /**
     * The solver that successfully solved the current path condition.
     * It is guaranteed to be one of the solvers in {@link #solvers}.
     */
    protected ProblemGeneral resultSolver;
    /**
     * Indicates whether the result of solving the path condition is satisfiable.
     * <code>true</code> if satisfiable, <code>false</code> otherwise.
     */
    protected Boolean result;
    /**
     * Parser that parsed the {@link #resultSolver} with the path condition.
     */
    public PCParser resultParser;
    /**
     * Map of solver names to their executor services.
     * Z3 solvers use single-thread executors because Z3 contexts
     * are not thread-safe and must run on the same thread.
     * Other solvers share a fixed thread pool.
     */
    public static Map<String, ExecutorService> executors;

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
        result = null;
        resultSolver = null;
        solvers = new ArrayList<>();
        List<String> dp = SymbolicInstructionFactory.dp;
        for (String s : dp) {
            solvers.add(createSolverFromDpString(s, pc));
        }

        Pair<Boolean, ProblemGeneral> pair = checkPathConditionSequentially(pc);
        result = pair.getKey();
        resultSolver = pair.getValue();

        if (result == null) {
            throw new SPFException("Error: no solver could parse or solve the path condition: " + pc + "\n");
        }

        if (SymbolicInstructionFactory.debugMode)
            System.out.println("numeric PC: " + pc + " -> " + result + "\n");

        if (SymbolicInstructionFactory.regressMode) {
            String output = "##NUMERIC PC: ";
            output = output + (result == Boolean.TRUE ? "(SOLVED)" : "(UNSOLVED)");
            output = output + " " + pc;
            System.out.println(output);
        }

        if (result == Boolean.TRUE) {
            return true;
        } else {
            return false;
        }

    }

    /**
     * Try to solve the given PathCondition using the configured solvers sequentially.
     * It stops as soon as one solver can parse and return a definite SAT/UNSAT result.
     *
     * When Choco is used with other solvers, its UNSAT is skipped
     * because its limited integer range can give unsound UNSAT results.
     *
     * @param pc the PathCondition to solve
     * @return a Pair of Boolean result and the solver instance that solved the PC.
     **/
    public Pair<Boolean, ProblemGeneral> checkPathConditionSequentially(PathCondition pc) {
        Boolean res = null;
        ProblemGeneral solver = null;
        for(int i = 0; i < solvers.size() && res == null; i++) {
            solver = solvers.get(i);
            if (SymbolicInstructionFactory.debugMode) {
                System.out.println("Using solver: " + solver.getClass().getSimpleName());
            }
            try {
                ProblemGeneral tempPb = PCParser.parse(pc, solver);
                if (tempPb == null) {
                    res = Boolean.FALSE;
                } else {
                    // YN: z3 optimize
                    if (Observations.lastObservedSymbolicExpression != null) {
                        if (solver instanceof ProblemZ3Optimize) {
                            ((ProblemZ3Optimize) solver).maximize(
                                    PCParser.getExpression((IntegerExpression) Observations.lastObservedSymbolicExpression));
                        }
                    }
                    res = solver.solve();
                    // Choco uses a reduced integer range [-21474836, 21474836].
                    // UNSAT results may be unsound for verification. skip when multiple solvers are available.
                    if (solvers.size() > 1 && solver instanceof ProblemChoco && res == false) {
                        res = null;
                    }
                }
            } catch (Exception e) {
                if (SymbolicInstructionFactory.debugMode) {
                    System.out.println("Exception in parsing or solving with solver"
                            + solver.getClass().getSimpleName() + ":" + e
                    );
                }
            }
        }
        return new Pair<Boolean, ProblemGeneral>(res, solver);
    }

    public boolean isSatisfiableParallel(PathCondition pc) {
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

        if(executors == null) {
           setupExecutors();
        }

        resultParser = null;
        result = null;

        List<String> dp = SymbolicInstructionFactory.dp;
        MultiExecutorCompletionService<ParallelSolverResult> completionService = new MultiExecutorCompletionService<>();
        List<Future<ParallelSolverResult>> futures = new ArrayList<>();

        // Submit one solver task per DP (decision procedure) in parallel
        for (int i = 0; i < dp.size(); i++) {
            ExecutorService executor = executors.get(dp.get(i));
            // Variable used in lambda expression should be final or effectively final
            final int tempI = i;
            // Submit a task to the appropriate executor;
            // each task parses and solves a PC in a separate thread of the appropriate executor
            Future<ParallelSolverResult> future = completionService.submit(executor, () -> {
                ProblemGeneral solver = null;
                PCParser parser = null;
                Boolean threadResult = null;
                try {
                    solver = createSolverFromDpString(dp.get(tempI), pc);
                    parser = new PCParser();
                    ProblemGeneral tempPb = parser.parse(pc, solver);
                    if (tempPb == null) {
                        threadResult = Boolean.FALSE;
                    } else {
                        // YN: z3 optimize
                        if (Observations.lastObservedSymbolicExpression != null) {
                            if (solver instanceof ProblemZ3Optimize) {
                                ((ProblemZ3Optimize) solver).maximize(
                                        parser.getExpression((IntegerExpression) Observations.lastObservedSymbolicExpression));
                            }
                        }
                        // If thread was interrupted (another solver already succeeded), stop early
                        if(Thread.currentThread().isInterrupted()) {
                            return null;
                        }
                        threadResult = solver.solve();
                    }
                    return new ParallelSolverResult(threadResult, solver, parser);
                } catch (Exception e) {
                    return new ParallelSolverResult(threadResult, solver, parser, e);
                } finally {
                    cleanup(solver);
                }
            });
            futures.add(future);
        }

        for(int i = 0; i < dp.size(); i++) {
            try {
                Future<ParallelSolverResult> future = completionService.take();
                ParallelSolverResult parallelResult = future.get();

                if(parallelResult == null) continue;

                if(parallelResult.exception != null && SymbolicInstructionFactory.debugMode) {
                    System.out.println("Exception in parsing or solving with solver"
                            + parallelResult.solver.getClass().getSimpleName() + ":" + parallelResult.exception
                    );
                    // continue if the future resulted in an exception
                    continue;
                }
                // skip if choco returns an UNSAT/false if more than one solver is used
                if (dp.size() > 1 && parallelResult.solver instanceof ProblemChoco && parallelResult.result == false) {
                    continue;
                }
                result = parallelResult.result;
                resultParser = parallelResult.parser;
                // Cancel all remaining solvers (since we already have an answer)
                for(Future<ParallelSolverResult> f : futures) {
                    if(!f.isDone()) {
                        f.cancel(true);
                    }
                }
                if (SymbolicInstructionFactory.debugMode) {
                    System.out.println("numeric PC: " + pc + " -> " + result + " solved by " + parallelResult.solver.getClass().getSimpleName() + "\n");
                }
                // stop after first valid result
                break;
            } catch (Exception e) {
                if(SymbolicInstructionFactory.debugMode) {
                    e.printStackTrace();
                }
            }
        }

        if (result == null) {
            throw new NoSolverSucceededException("Error: no solver could parse or solve the path condition: " + pc + "\n");
        }


        if (SymbolicInstructionFactory.regressMode) {
            String output = "##NUMERIC PC: ";
            output = output + (result == Boolean.TRUE ? "(SOLVED)" : "(UNSOLVED)");
            output = output + " " + pc;
            System.out.println(output);
        }

        return result;
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
        if (solvers == null) return;
        for (ProblemGeneral pb : solvers) {
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
    }

    public void cleanup(ProblemGeneral pb) {
        if (pb == null) return;
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

        List<String> dp = SymbolicInstructionFactory.dp;
        if (dp.contains("no_solver"))
            return true;

        if (isSatisfiable(pc)) {

            // compute solutions for real variables:
            Set<Entry<SymbolicReal, Object>> sym_realvar_mappings = resultParser.symRealVar.entrySet();
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
                sym_realvar_mappings = resultParser.symRealVar.entrySet();
                i_real = sym_realvar_mappings.iterator();
                while (i_real.hasNext()) {
                    Entry<SymbolicReal, Object> e = i_real.next();
                    SymbolicReal pcVar = e.getKey();
                    Object dpVar = e.getValue();
                    pcVar.solution = resultSolver.getRealValue(dpVar); // may be undefined: throws an exception
                }
            } catch (Exception exp) {
                this.catchBody(resultParser.symRealVar, resultSolver, pc);
            } // end catch

            // compute solutions for integer variables
            Set<Entry<SymbolicInteger, Object>> sym_intvar_mappings = resultParser.symIntegerVar.entrySet();
            Iterator<Entry<SymbolicInteger, Object>> i_int = sym_intvar_mappings.iterator();
            // try {
            while (i_int.hasNext()) {
                Entry<SymbolicInteger, Object> e = i_int.next();
                e.getKey().solution = resultSolver.getIntValue(e.getValue());

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

        List<String> dp = SymbolicInstructionFactory.dp;
        if (dp.contains("no_solver")) {
            return result;
        }

        if (isSatisfiable(pc)) {

            // compute solutions for real variables:
            Set<Entry<SymbolicReal, Object>> sym_realvar_mappings = resultParser.symRealVar.entrySet();
            Iterator<Entry<SymbolicReal, Object>> i_real = sym_realvar_mappings.iterator();

            try {
                sym_realvar_mappings = resultParser.symRealVar.entrySet();
                i_real = sym_realvar_mappings.iterator();
                while (i_real.hasNext()) {
                    Entry<SymbolicReal, Object> e = i_real.next();
                    SymbolicReal pcVar = e.getKey();
                    Object dpVar = e.getValue();
                    double e_value = resultSolver.getRealValue(dpVar); // may be undefined: throws an exception
                    pcVar.solution = e_value; 
                    result.put(pcVar.getName(), e_value);
                }
            } catch (Exception exp) {
                this.catchBody(resultParser.symRealVar, resultSolver, pc);
            }

            // compute solutions for integer variables
            Set<Entry<SymbolicInteger, Object>> sym_intvar_mappings = resultParser.symIntegerVar.entrySet();
            Iterator<Entry<SymbolicInteger, Object>> i_int = sym_intvar_mappings.iterator();
            // try {
            while (i_int.hasNext()) {
                Entry<SymbolicInteger, Object> e = i_int.next();
                long e_value = resultSolver.getIntValue(e.getValue());
                e.getKey().solution = e_value;
                result.put(e.getKey().getName(), e_value);

            }
            cleanup();
            return result;
        } else {
            return result;
        }
    }

    private static ProblemGeneral createSolverFromDpString(String s, PathCondition pc) {
        switch (s) {
            case "choco":
                return new ProblemChoco();
//            case "choco2":
//                return new ProblemChoco2();
            case "coral":
                return new ProblemCoral();
            case "iasolver":
                return new ProblemIAsolver();
            case "cvc3":
                return new ProblemCVC3();
            case "cvc3bitvec":
                return new ProblemCVC3BitVector();
            case "yices":
                return new ProblemYices();
            case "z3":
                return new ProblemZ3();
            case "z3inc":
                return new ProblemZ3Incremental();
            case "z3bitvectorinc":
                return new ProblemZ3BitVectorIncremental();
            case "debug":
                return new DebugSolvers(pc);
//            case "compare":
//                return new ProblemCompare(pc, this);
            case "z3bitvector":
                return new ProblemZ3BitVector();
            case "z3optimize":
                return new ProblemZ3Optimize();
            default:
                throw new RuntimeException(
                        "## Error: unknown decision procedure " + s + "\n(use choco or IAsolver or CVC3)");
        }
    }

    /**
     * Initializes executors for all solvers.
     * Z3 (and its variants) solvers get single-thread executors since contexts are not thread-safe.
     * Other solvers share a fixed pool sized to the number of solvers.
     */
    private static void setupExecutors() {
        List<String> dp = SymbolicInstructionFactory.dp;
        executors = new HashMap<>();
        Set<String> dpSet = new HashSet<>(dp);
        for(String s : dp) {
            if(s.equals("z3") || s.equals("z3inc") || s.equals("z3bitvectorinc") || s.equals("z3bitvector") || s.equals("z3optimize")) {
                executors.put(s, Executors.newSingleThreadExecutor(
                        (Runnable r) -> {
                            Thread t = Executors.defaultThreadFactory().newThread(r);
                            t.setDaemon(true);
                            return t;
                        }
                ));
                dpSet.remove(s);
            }
        }

        if(!dpSet.isEmpty()) {
            ExecutorService executor = Executors.newFixedThreadPool(dpSet.size(),
                    (Runnable r) -> {
                        Thread t = Executors.defaultThreadFactory().newThread(r);
                        t.setDaemon(true);
                        return t;
                    }
            );
            for(String s : dpSet) {
                executors.put(s, executor);
            }
        }
    }

    /**
     * Shuts down all executors in an orderly way.
     * For Z3 solvers, submits a cleanup task to close native contexts
     * before shutting down. Waits up to 20s for tasks to finish, then
     * forces shutdown if needed.
     */
    public static void cleanExecutors() {
        List<String> dp = SymbolicInstructionFactory.dp;
        if(!SymbolicInstructionFactory.parallelModeEnabled || executors == null) return;
        for(String s : executors.keySet()) {
            ExecutorService executorService = executors.get(s);
            if(executorService.isShutdown()) continue;
            if(s.equals("z3") || s.equals("z3inc") || s.equals("z3bitvectorinc") || s.equals("z3bitvector") || s.equals("z3optimize")) {
                executorService.submit(() -> {
                    ProblemGeneral solver = createSolverFromDpString(s, new PathCondition());
                    if(solver instanceof ProblemZ3) {
                        ((ProblemZ3) solver).closeContext();
                    } else if(solver instanceof ProblemZ3Optimize) {
                        ((ProblemZ3Optimize) solver).closeContext();
                    } else if (solver instanceof ProblemZ3BitVector) {
                        ((ProblemZ3BitVector) solver).closeContext();
                    } else if(solver instanceof ProblemZ3Incremental) {
                        ((ProblemZ3Incremental) solver).closeContext();
                    } else {
                        ((ProblemZ3BitVectorIncremental) solver).closeContext();
                    }
                });
            }
            try {
                executorService.shutdown();
                executorService.awaitTermination(10, TimeUnit.SECONDS);
            } catch (InterruptedException e) {

            }
        }
    }

}

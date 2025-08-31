package gov.nasa.jpf.symbc.numeric;

import gov.nasa.jpf.symbc.numeric.solvers.ProblemGeneral;

/**
 * Holds the result of running a solver in parallel.
 * Contains the satisfiability result, the solver used,
 * and the parser that processed the solver with the path condition.
 */
public class ParallelSolverResult {
    public Boolean result;
    public ProblemGeneral solver;
    public PCParser parser;
    public Exception exception;

    public ParallelSolverResult(Boolean result, ProblemGeneral solver, PCParser parser, Exception e) {
        this.result = result;
        this.solver = solver;
        this.parser = parser;
        this.exception = e;
    }

    public ParallelSolverResult(Boolean result, ProblemGeneral solver, PCParser parser) {
        this.result = result;
        this.solver = solver;
        this.parser = parser;
    }
}

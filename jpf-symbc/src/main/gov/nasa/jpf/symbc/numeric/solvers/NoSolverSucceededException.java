package gov.nasa.jpf.symbc.numeric.solvers;

public class NoSolverSucceededException extends RuntimeException {

    public NoSolverSucceededException(String message) {
        super(message);
    }

}

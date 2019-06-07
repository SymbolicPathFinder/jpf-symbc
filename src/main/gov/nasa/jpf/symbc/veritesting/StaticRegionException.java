package gov.nasa.jpf.symbc.veritesting;

import com.ibm.wala.shrikeCT.InvalidClassFileException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;

import java.util.HashMap;

/**
 * Exception class used whenever violation was detected during veritesting.
 */
public class StaticRegionException extends Exception {

    // Maps each exception's message to that exception's count of how often it was thrown
    public static HashMap<String, Pair<Integer, ExceptionPhase>> ExceptionMap = new HashMap<>();
    private static boolean staticAnalysisComplete = false;

    public StaticRegionException(String reason) {
        super(reason);
    }

    public static void staticAnalysisComplete() {
        staticAnalysisComplete = true;
    }

    public enum ExceptionPhase {
        STATIC("StaticAnalysisPhase"), INSTANTIATION("InstantiationPhase"), DONTKNOW("Unknown phase");
        String name;
        ExceptionPhase(String staticAnalysisPhase) {
            name = staticAnalysisPhase;
        }
        public String toString() { return name; }
    }

    public static void throwException(StaticRegionException sre, ExceptionPhase phase) throws StaticRegionException {
        countException(sre, phase);
        throw sre;
    }

    public static void throwException(IllegalArgumentException sre, ExceptionPhase phase) throws IllegalArgumentException {
        countException(sre, phase);
        throw sre;
    }


    private static void countException(Exception sre, ExceptionPhase phase) {
//        if (phase == ExceptionPhase.STATIC && staticAnalysisComplete)
//            assert(false);
        if (ExceptionMap.containsKey(sre.getMessage())) {
            Pair<Integer, ExceptionPhase> p = ExceptionMap.get(sre.getMessage());
            // assumes exceptional messages are not shared between phases.
            // If this assumption doesn't hold, we need to include phase in the key of ExceptionMap.
            assert phase == p.getSecond() || phase == ExceptionPhase.DONTKNOW || p.getSecond() == ExceptionPhase.DONTKNOW;
            ExceptionMap.put(sre.getMessage(), new Pair(p.getFirst()+1, phase));
        } else {
            ExceptionMap.put(sre.getMessage(), new Pair(1, phase));
        }
    }

}

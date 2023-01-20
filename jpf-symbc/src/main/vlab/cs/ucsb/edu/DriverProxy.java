package vlab.cs.ucsb.edu;

import java.math.BigInteger;
import java.util.Map;

/**
 * ABC Java Interface
 * 
 * set JVM argument -Djava.library.path=/usr/local/lib or set env. variable
 * LD_LIBRARY_PATH to make sure 'libabc' is available to JVM
 * 
 * @author baki
 *
 */
public class DriverProxy {
    public enum Option {
        USE_SIGNED_INTEGERS(0),             // default option
        USE_UNSIGNED_INTEGERS(1), 
        USE_MULTITRACK_AUTO(2),             // default option
        USE_SINGLETRACK_AUTO(3), 
        ENABLE_EQUIVALENCE_CLASSES(4),      // default option
        DISABLE_EQUIVALENCE_CLASSES(5), 
        ENABLE_DEPENDENCY_ANALYSIS(6),      // default option
        DISABLE_DEPENDENCY_ANALYSIS(7), 
        ENABLE_IMPLICATIONS(8),             // default option
        DISABLE_IMPLICATIONS(9),
        LIMIT_LEN_IMPLICATIONS(10),
        ENABLE_SORTING_HEURISTICS(11),      // default option
        DISABLE_SORTING_HEURISTICS(12), 
        REGEX_FLAG(13),
        OUTPUT_PATH(14),                    // not actively used through Java
        SCRIPT_PATH(15);                    // not actively used

        private final int value;

        private Option(int value) {
            this.value = value;
        }

        public int getValue() {
            return this.value;
        }
        
        /**
         * Syntax flag, enables intersection (<tt>&amp;</tt>).
         */
        public static final int REGEX_FLAG_INTERSECTION = 0x0001;

        /**
         * Syntax flag, enables complement (<tt>~</tt>).
         */
        public static final int REGEX_FLAG_COMPLEMENT = 0x0002;
        
        /**
         * Syntax flag, enables empty language (<tt>#</tt>).
         */
        public static final int REGEX_FLAG_EMPTY = 0x0004;
        
        /**
         * Syntax flag, enables anystring (<tt>@</tt>).
         */
        public static final int REGEX_FLAG_ANYSTRING = 0x0008;
        
        /**
         * Syntax flag, enables named automata (<tt>&lt;</tt>identifier<tt>&gt;</tt>).
         */
        public static final int REGEX_FLAG_AUTOMATON = 0x0010;
        
        /**
         * Syntax flag, enables numerical intervals (<tt>&lt;<i>n</i>-<i>m</i>&gt;</tt>).
         */
        public static final int REGEX_FLAG_INTERVAL = 0x0020;
        
        /**
         * Syntax flag, enables all optional RegularExpression syntax.
         */
        public static final int REGEX_FLAG_ALL = 0xffff;
        
        /**
         * Syntax flag, enables no optional RegularExpression syntax.
         */
        public static final int REGEX_FLAG_NONE = 0x0000;
    }

    private long driverPointer;
    
    static {
        System.loadLibrary("abc");
    }

    public DriverProxy() {
        initABC(0);
    }

    public DriverProxy(final int logLevel) {
        initABC(logLevel);
    }
    
    public void setOption(final Option option) {
        setOption(option.getValue());
    }

    public void setOption(final Option option, final int value) {
        setOption(option.getValue(), value);
    }
    
    public void setOption(final Option option, final String value) {
        setOption(option.getValue(), value);
    }

    private native void initABC(final int logFlag);

    private native void setOption(final int option);
    
    private native void setOption(final int option, final int value);

    private native void setOption(final int option, final String value);

    public native boolean isSatisfiable(final String constraint);

    public native BigInteger countVariable(final String varName, final long bound);
    
    public native BigInteger countInts(final long bound);
    
    public native BigInteger countStrs(final long bound);
    
    public native BigInteger count(final long intBound, final long strBound);
    
    public native byte[] getModelCounterForVariable(final String varName);
    
    public native byte[] getModelCounter();

    public native BigInteger countVariable(final String varName, final long bound, final byte[] modelCounter);
    
    public native BigInteger countInts(final long bound, final byte[] modelCounter);
    
    public native BigInteger countStrs(final long bound, final byte[] modelCounter);

    public native BigInteger count(final long intBound, final long strBound, final byte[] modelCounter);

    public native void printResultAutomaton();

    public native void printResultAutomaton(String filePath);

    public native Map<String, String> getSatisfyingExamples();

    public native void reset();

    public native void dispose();
}

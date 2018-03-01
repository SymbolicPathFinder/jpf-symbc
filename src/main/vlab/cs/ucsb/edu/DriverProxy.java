package vlab.cs.ucsb.edu;

import java.math.BigDecimal;
import java.util.Map;

/**
 * ABC Java Interface
 * 
 * set JVM argument -Djava.library.path=/usr/local/lib or set env. variable
 * LD_LIBRARY_PATH to make sure 'libabc' is available to JVM
 * 
 * @author baki
 *
 * TODO add more flexibility to constraint construction 
 * TODO check for JVM (JNI) thread issues
 */
public class DriverProxy {
    public enum Option {
	OUTPUT_PATH(0), MODEL_COUNTER_ENABLED(1), LIA_ENGINE_ENABLED(2), SCRIPT_PATH(3), 
	LIA_ONLY_CONSTRAINT(4), LIA_NATURAL_NUMBERS_ONLY(5);

	private final int value;

	private Option(int value) {
	    this.value = value;
	}

	public int getValue() {
	    return this.value;
	}
    }

    private long driverPointer;
    private static final String ARITHMETIC_VARIABLE = "__VLAB_CS_ARITHMETIC__";

    static {
	System.loadLibrary("abc");
    }

    public DriverProxy() {
	initABC(0);
    }

    public DriverProxy(int logFlag) {
	initABC(logFlag);
    }
    
    public BigDecimal count(double bound) {
	return count(ARITHMETIC_VARIABLE, bound, false);
    } 

    public BigDecimal count(String var_name, int bound) {
	return count(var_name, bound, true);
    }
    
    private BigDecimal count(String var_name, double bound) {
	return count(var_name, bound, true);
    }

    public BigDecimal count(String var_name, double bound, boolean countLessThanOrEqualToBound) {
	String resultString = countVar(var_name, bound, countLessThanOrEqualToBound).trim();
	BigDecimal result;

	try {
	    result = new BigDecimal(resultString);
	} catch (NumberFormatException e) {
	    result = null;
	}
	return result;
    }
    
    public BigDecimal symbolicCount(double bound) {
	return symbolicCount(ARITHMETIC_VARIABLE, bound, false);
    } 

    public BigDecimal symbolicCount(String var_name, int bound) {
	return symbolicCount(var_name, bound, true);
    }
    
    private BigDecimal symbolicCount(String var_name, double bound) {
	return symbolicCount(var_name, bound, true);
    }
    
    public BigDecimal symbolicCount(String var_name, double bound, boolean countLessThanOrEqualToBound) {
	String resultString = symbolicCountVar(var_name, bound, countLessThanOrEqualToBound).trim();
	BigDecimal result;

	try {
	    result = new BigDecimal(resultString);
	} catch (NumberFormatException e) {
	    result = null;
	}
	return result;
    }

    public void setOption(Option option, boolean value) {
	setOption(option.getValue(), value);
    }

    public void setOption(Option option, String value) {
	setOption(option.getValue(), value);
    }

    private native void initABC(int logFlag);

    private native void setOption(int option, boolean value);

    private native void setOption(int option, String value);

    public native boolean isSatisfiable(String constraint);

    private native String countVar(String var_name, double bound, boolean countLessThanOrEqualToBound);
    
    private native String symbolicCountVar(String var_name, double bound, boolean countLessThanOrEqualToBound);

    public native void printResultAutomaton();

    public native void printResultAutomaton(String filePath);

    public native Map<String, String> getSatisfyingExamples();

    public native void reset();

    public native void dispose();
}

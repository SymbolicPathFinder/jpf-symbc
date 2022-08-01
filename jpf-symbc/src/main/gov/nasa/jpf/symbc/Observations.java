package gov.nasa.jpf.symbc;

import gov.nasa.jpf.symbc.numeric.Expression;

public class Observations {
    
    /** Used for user-defined cost. */
	public static double lastObservedCost = 0.0;
    
	/** Used for maximization of user-defined cost. */
	public static Expression lastObservedSymbolicExpression = null;
	
	/** Used to set current input size in side-channel analysis in order to generate correct input file. */
    public static int lastObservedInputSize = -1;
    
    /** Used by MetricListener to propagate last measured metric value. */
    public static double lastMeasuredMetricValue = 0.0;
    
    public static void reset() {
        lastObservedCost = 0.0;
        lastObservedSymbolicExpression = null;
        lastObservedInputSize = -1;
        lastMeasuredMetricValue = 0.0;
    }
}

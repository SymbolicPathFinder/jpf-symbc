package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import za.ac.sun.cs.green.expr.Expression;

public abstract class FixedPointAstMapVisitor extends AstMapVisitor{
    /**
     * This is used to capture the fact that there is change happening in the transformation, this is used for the
     * quick check for the fix point computation.
     */
    protected boolean somethingChanged;

    /**
     * this is used when computing fixed point to carry the first exception that the visitor might have encountered.
     */
    protected Exception firstException;


    protected DynamicRegion instantiatedRegion;

    public boolean getChange(){return somethingChanged;}

    public Exception getFirstException() {
        return firstException;
    }

    public FixedPointAstMapVisitor(ExprVisitor<Expression> exprVisitor) {
        super(exprVisitor);
    }

    public abstract DynamicRegion execute();
}

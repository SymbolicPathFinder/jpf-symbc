package gov.nasa.jpf.symbc.veritesting.ast.visitors;


import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;

/**
 * An interface for visiting all expression in RangerIR.
 *
 */
public interface ExprVisitor<T> {
    public T visit(IntConstant expr);
    public T visit(IntVariable expr);
    public T visit(Operation expr);
    public T visit(RealConstant expr);
    public T visit(RealVariable expr);
    public T visit(StringConstantGreen expr);
    public T visit(StringVariable expr);
    public T visit(IfThenElseExpr expr);
    public T visit(ArrayRefVarExpr expr);
    public T visit(WalaVarExpr expr);
    public T visit(FieldRefVarExpr expr);
    public T visit(GammaVarExpr expr);
    public T visit(AstVarExpr expr);
}

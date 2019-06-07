package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;

/**
 * An interface for visiting all Statements in RangerIR.
 *
 */
public interface AstVisitor<T>  {

    T visit(AssignmentStmt a);
    T visit(CompositionStmt a);
    T visit(IfThenElseStmt a);
    T visit(SkipStmt a);
    T visit(SPFCaseStmt c);

    T visit(ArrayLoadInstruction c);
    T visit(ArrayStoreInstruction c);
    T visit(SwitchInstruction c);
    T visit(ReturnInstruction c);
    T visit(GetInstruction c);
    T visit(PutInstruction c);
    T visit(NewInstruction c);
    T visit(InvokeInstruction c);
    T visit(ArrayLengthInstruction c);
    T visit(ThrowInstruction c);
    T visit(CheckCastInstruction c);
    T visit(InstanceOfInstruction c);
    T visit(PhiInstruction c);

}

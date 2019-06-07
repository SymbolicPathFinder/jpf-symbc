package gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingMain.skipRegionStrings;
import static gov.nasa.jpf.symbc.veritesting.ast.def.SkipStmt.skip;


public class NoSkipVisitor implements AstVisitor<Stmt> {


    @Override
    public Stmt visit(AssignmentStmt a) {
        return a;
    }

    @Override
    public Stmt visit(CompositionStmt a) {
        Stmt leftStmt = a.s1.accept(this);
        Stmt rightStmt = a.s2.accept(this);
        if ((leftStmt instanceof SkipStmt) && (rightStmt instanceof SkipStmt))
            return skip;
        else if((leftStmt instanceof SkipStmt) && !(rightStmt instanceof SkipStmt))
            return rightStmt;
        else if(!(leftStmt instanceof SkipStmt) && (rightStmt instanceof SkipStmt))
            return leftStmt;
        else
            return new CompositionStmt(leftStmt, rightStmt);
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        return bad(a);
    }

    @Override
    public Stmt visit(SkipStmt a) {
        return a;
    }

    @Override
    public Stmt visit(SPFCaseStmt c) {
        return bad(c);
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(SwitchInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(ReturnInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(GetInstruction c) {
        return null;
    }

    @Override
    public Stmt visit(PutInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(NewInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(InvokeInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(ThrowInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(InstanceOfInstruction c) {
        return bad(c);
    }

    @Override
    public Stmt visit(PhiInstruction c) {
        return bad(c);
    }

    public Stmt bad(Object obj) {
        String name = obj.getClass().getCanonicalName();
        String exceptionalReason = "Unsupported class: " + name +
                " value: " + obj.toString() + " seen in NoSkipVisitor";
        skipRegionStrings.add(exceptionalReason);
        throwException(new IllegalArgumentException(exceptionalReason), INSTANTIATION);
        return (Stmt)obj;
    }
}

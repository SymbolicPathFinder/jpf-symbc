package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;

import java.util.function.BinaryOperator;


/*
    Preconditions:
        defaultVal should be a 'zero' element for combine.  That is:
            combine(V, defaultVal) = V;
        Also, combine should be commutative and associative.
 */

public class AstIterVisitor<T> extends ExprMapVisitor implements AstVisitor<T> {

    protected final ExprVisitor<T> exprVisitor;
    protected final BinaryOperator<T> combine;
    protected final T defaultVal;
    protected final ExprVisitorAdapter<T> eva;

    public AstIterVisitor(ExprVisitor<T> exprVisitor,
                          BinaryOperator<T> combine,
                          T defaultVal) {
        this.eva = new ExprVisitorAdapter<T>(exprVisitor);
        this.exprVisitor = exprVisitor;
        this.combine = combine;
        this.defaultVal = defaultVal;
    }

    @Override
    public T visit(AssignmentStmt a) {
        return combine.apply(eva.accept(a.lhs), eva.accept(a.rhs));
    }

    @Override
    public T visit(CompositionStmt a) {
        return combine.apply(a.s1.accept(this), a.s2.accept(this));

    }

    @Override
    public T visit(IfThenElseStmt a) {
        return combine.apply(eva.accept(a.condition),
                combine.apply(a.thenStmt.accept(this), a.elseStmt.accept(this)));
    }

    @Override
    public T visit(SkipStmt a) {
        return defaultVal;
    }

    @Override
    public T visit(SPFCaseStmt c) {
        return (eva.accept(c.spfCondition));
    }

    @Override
    public T visit(ArrayLoadInstruction c) {
        return combine.apply(eva.accept(c.arrayref),
                combine.apply(eva.accept(c.index),
                              eva.accept(c.def)));
    }

    @Override
    public T visit(ArrayStoreInstruction c) {
        return combine.apply(eva.accept(c.arrayref),
                combine.apply(eva.accept(c.index),
                              eva.accept(c.assignExpr)));
    }

    @Override
    public T visit(SwitchInstruction c) {
        return defaultVal;
    }

    @Override
    public T visit(ReturnInstruction c) {
        return eva.accept(c.rhs);
    }

    @Override
    public T visit(GetInstruction c) {
        return combine.apply(eva.accept(c.def),
                eva.accept(c.ref));
    }

    @Override
    public T visit(PutInstruction c) {
        return combine.apply(eva.accept(c.def),
                eva.accept(c.assignExpr));
    }

    @Override
    public T visit(NewInstruction c) {
        return defaultVal;
    }

    @Override
    public T visit(InvokeInstruction c) {
        T toReturn = defaultVal;

        for (Expression e: c.result) {
            toReturn = combine.apply(toReturn, eva.accept(e));
        }
        for (Expression e: c.params) {
            toReturn = combine.apply(toReturn, eva.accept(e));
        }
        return toReturn;
    }

    @Override
    public T visit(ArrayLengthInstruction c) {
        return combine.apply(eva.accept(c.def),
                eva.accept(c.arrayref));
    }

    @Override
    public T visit(ThrowInstruction c) {
        return defaultVal;
    }

    @Override
    public T visit(CheckCastInstruction c) {
        return combine.apply(eva.accept(c.result),
                eva.accept(c.val));
    }

    @Override
    public T visit(InstanceOfInstruction c) {
        return combine.apply(eva.accept(c.result),
                eva.accept(c.val));
    }

    @Override
    public T visit(PhiInstruction c) {
        T toReturn = eva.accept(c.def);
        for (Expression e: c.rhs) {
            toReturn = combine.apply(toReturn, eva.accept(e));
        }
        return toReturn;
    }

}

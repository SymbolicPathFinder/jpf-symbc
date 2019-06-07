package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

/**
 * This visitor visits all statements to find the first use of every stack slot.
 */

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprRegionInputVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import za.ac.sun.cs.green.expr.Expression;

import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.DefUseVisit.DEF;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.DefUseVisit.USE;

public class RegionInputVisitor extends AstMapVisitor{

    ExprRegionInputVisitor exprRegionInputVisitor;
    public RegionInputVisitor(ExprRegionInputVisitor exprRegionInputVisitor) {
        super(exprRegionInputVisitor);
        this.exprRegionInputVisitor = exprRegionInputVisitor;
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(a.rhs);

        exprRegionInputVisitor.defUseVisit = DEF;
        eva.accept(a.lhs);
        return null;
    }

    @Override
    public Stmt visit(CompositionStmt a) {
        a.s1.accept(this);
        a.s2.accept(this);
        return null;

    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(a.condition);
        a.thenStmt.accept(this);
        a.elseStmt.accept(this);
        return null;
    }

    @Override
    public Stmt visit(SkipStmt a) {
        return null;
    }

    @Override
    public Stmt visit(SPFCaseStmt c) {
        return null;
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(c.arrayref);
        eva.accept(c.index);
        exprRegionInputVisitor.defUseVisit = DEF;
        eva.accept(c.def);
        return null;
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(c.arrayref);
        eva.accept(c.index);
        eva.accept(c.assignExpr);
        return null;
    }

    @Override
    public Stmt visit(SwitchInstruction c) {
        return null;
    }

    @Override
    public Stmt visit(ReturnInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(c.rhs);
        return null;
    }

    @Override
    public Stmt visit(GetInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(c.ref);

        exprRegionInputVisitor.defUseVisit = DEF;
        eva.accept(c.def);
        return null;
    }

    @Override
    public Stmt visit(PutInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(c.def);
        eva.accept(c.assignExpr);
        return null;
    }

    @Override
    public Stmt visit(NewInstruction c) {
        return null;
    }

    @Override
    public Stmt visit(InvokeInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        Expression [] params = new Expression [c.params.length];
        for (int i=0; i < params.length; i++) {
            params[i] = eva.accept(c.params[i]);
        }
        exprRegionInputVisitor.defUseVisit = DEF;
        Expression [] result = new Expression [c.result.length];
        for (int i=0; i < result.length; i++) {
            result[i] = eva.accept(c.result[i]);
        }

        return null;
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(c.arrayref);

        exprRegionInputVisitor.defUseVisit = DEF;
        eva.accept(c.def);
        return null;
    }

    @Override
    public Stmt visit(ThrowInstruction c) {
        return null;
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(c.val);

        exprRegionInputVisitor.defUseVisit = DEF;
        eva.accept(c.result);
        return null;
    }

    @Override
    public Stmt visit(InstanceOfInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        eva.accept(c.val);

        exprRegionInputVisitor.defUseVisit = DEF;
        eva.accept(c.result);
        return null;
    }

    @Override
    public Stmt visit(PhiInstruction c) {
        exprRegionInputVisitor.defUseVisit = USE;
        Expression [] rhs = new Expression[c.rhs.length];
        for (int i=0; i < rhs.length; i++) {
            rhs[i] = eva.accept(c.rhs[i]);
        }

        exprRegionInputVisitor.defUseVisit = DEF;
        eva.accept(c.def);

        return null;
    }
}

package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;


import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprBoundaryVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;

import java.util.ArrayList;
import java.util.Collections;

/**
 * The visitor explores the boundaries of the region by identifying: first def, last def and first use vars. This information is later used to identify beginning and ending of vars for which the tables should be populated.
 */

public class RegionBoundaryVisitor extends AstMapVisitor {

    private ArrayList<Integer> allDefs = new ArrayList<>();


    public RegionBoundaryVisitor(ExprBoundaryVisitor exprBoundaryVisitor) {
        super(exprBoundaryVisitor);
    }


    @Override
    public Stmt visit(AssignmentStmt a) {
        if (a.lhs instanceof WalaVarExpr) {
            allDefs.add(((WalaVarExpr) a.lhs).number);
            eva.accept(a.rhs);
        }
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
        allDefs.add(((WalaVarExpr) c.def).number);
        eva.accept(c.arrayref);
        eva.accept(c.index);
        return null;
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
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
        if (c.getOriginal().hasDef()) {
            allDefs.add(c.getOriginal().getDef());
        }
        eva.accept(c.rhs);
        return null;
    }

    @Override
    public Stmt visit(GetInstruction c) {
        allDefs.add(((WalaVarExpr) c.def).number);
        eva.accept(c.ref);
        return null;
    }

    @Override
    public Stmt visit(PutInstruction c) {
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
        if ((c.getOriginal()).getNumberOfReturnValues() != 0) {
            allDefs.add(c.getOriginal().getDef());
        }
        for (int i = 0; i < c.params.length; i++) {
            eva.accept(c.params[i]);
        }
        return null;
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        allDefs.add(((WalaVarExpr) c.def).number);
        eva.accept(c.arrayref);
        return null;
    }

    @Override
    public Stmt visit(ThrowInstruction c) {
        return null;
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        allDefs.add(c.getOriginal().getDef());
        eva.accept(c.val);
        return null;
    }

    @Override
    public Stmt visit(InstanceOfInstruction c) {
        allDefs.add(((WalaVarExpr) c.result).number);
        eva.accept(c.val);

        return null;
    }

    @Override
    public Stmt visit(PhiInstruction c) {
        allDefs.add(((WalaVarExpr) c.def).number);
        for (int i = 0; i < c.rhs.length; i++) {
            eva.accept(c.rhs[i]);
        }

        return null;
    }


    public RegionBoundaryOutput getOutput() {
        return new RegionBoundaryOutput(allDefs, (ExprBoundaryVisitor)exprVisitor);
    }
}

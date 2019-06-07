package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import jkind.lustre.*;
import jkind.lustre.Ast;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;
import java.util.List;

public class EquationVisitor extends ExprMapVisitor implements AstVisitor<Ast> {

    protected final ExprVisitor<Ast> exprVisitor;
    protected final ExprVisitorAdapter<Ast> eva;
    private ArrayList<Equation> equationList = new ArrayList<>();


    private EquationVisitor(ExprVisitor<Ast> exprVisitor) {
        this.eva = new ExprVisitorAdapter<Ast>(exprVisitor);
        this.exprVisitor = exprVisitor;
    }

    @Override
    public Ast visit(AssignmentStmt a) {
        Ast rhs = eva.accept(a.rhs);
        IdExpr lhs = new IdExpr(a.lhs.toString());
        equationList.add(new Equation(lhs, (Expr) rhs));
        return null;
    }

    @Override
    public Ast visit(CompositionStmt a) {
        a.s1.accept(this);
        a.s2.accept(this);
        return null;
    }


    @Override
    public Ast visit(IfThenElseStmt a) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(SkipStmt a) {
        return null;
    }

    @Override
    public Ast visit(SPFCaseStmt c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ArrayLoadInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ArrayStoreInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(SwitchInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ReturnInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(GetInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(PutInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(NewInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(InvokeInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ArrayLengthInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ThrowInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(CheckCastInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(InstanceOfInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(PhiInstruction c) {
        assert false;
        return null;
    }

    public static ArrayList<Equation> execute(DynamicRegion dynRegion) {
        EquationExprVisitor equationExprVisitor = new EquationExprVisitor(dynRegion);
        EquationVisitor equationVisitor = new EquationVisitor(equationExprVisitor);
        dynRegion.dynStmt.accept(equationVisitor);
        return equationVisitor.equationList;
    }
}

package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Triple;
import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLoadInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.GetInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;


/*
This visitor creates a list of all GetInstruction and ArrayLoadInstructions that appear before the first IfThenElseStmt
in a summary. The WalaVarExpr variables defined by these  "load" instructions are then removed from the list of
WalaVarExpr variables that appear in the first IfThenElseStmt's condition by SymbCondVisitor. SymbCondVisitor will
then be able to find all WalaVarExpr variables for which no stack slots are present.
 */
public class FirstITEStmtVisitor extends AstMapVisitor {
    public Expression condition = null;
    public ArrayList<GetInstruction> getInsns;
    public ArrayList<ArrayLoadInstruction> arrayLoadInsns;

    public FirstITEStmtVisitor() {
        super(new ExprMapVisitor());
        getInsns = new ArrayList<>();
        arrayLoadInsns = new ArrayList<>();
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        if (condition == null) condition = a.condition;
        return a;
    }

    @Override
    public Stmt visit(GetInstruction c) {
        if (condition == null) getInsns.add(c);
        return c;
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        if (condition == null) arrayLoadInsns.add(c);
        return c;
    }

    public static Triple<Expression, ArrayList<GetInstruction>, ArrayList<ArrayLoadInstruction>> execute(Stmt staticStmt) {
        FirstITEStmtVisitor visitor = new FirstITEStmtVisitor();
        staticStmt.accept(visitor);
        return new Triple<>(visitor.condition, visitor.getInsns, visitor.arrayLoadInsns);
    }
}

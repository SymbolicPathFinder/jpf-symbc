package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.ast.def.AssignmentStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class DeclarationStmtVisitor extends AstMapVisitor{
    public DeclarationStmtVisitor(ExprVisitor<Expression> exprVisitor) {
        super(exprVisitor);
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        return new AssignmentStmt(eva.accept(a.lhs), a.rhs);
    }
}

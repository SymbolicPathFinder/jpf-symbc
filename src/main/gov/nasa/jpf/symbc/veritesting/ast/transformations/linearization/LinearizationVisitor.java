package gov.nasa.jpf.symbc.veritesting.ast.transformations.linearization;

import gov.nasa.jpf.symbc.veritesting.ast.def.CompositionStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;

/**
 * Linearalize region statement by removing "If" Statements and embedding statements on the "then" and the "else" side, to become one stream of composition statements.
 *Assumptions: there are no more \phi functions, and every join
 // point for variable definitions is represented by a \Gamma function
 *
 */

public class LinearizationVisitor extends AstMapVisitor {

    public LinearizationVisitor() {
        super(new ExprMapVisitor());
    }

    public Stmt visit(IfThenElseStmt stmt) {
        Stmt thenStmt = stmt.thenStmt.accept(this);
        Stmt elseStmt = stmt.elseStmt.accept(this);
        return new CompositionStmt(thenStmt, elseStmt);
    }
}

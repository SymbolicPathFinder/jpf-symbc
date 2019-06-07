package gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

import java.util.LinkedList;

/**
 *This class flattens statement lists like ((s1; s2); (s3; s4)) into a "flat" list like: (s1; (s2; (s3; s4)))).

 It is accessed through a static method called flattenStmt.

 */
public class FlattenStmtListVisitor implements AstVisitor<Void> {

    public LinkedList<Stmt> stmtList = new LinkedList<Stmt>();

    private FlattenStmtListVisitor() {  }

    private Stmt extract() {
        if (stmtList.isEmpty()) {
            return SkipStmt.skip;
        } else if (stmtList.size() == 1) {
            return stmtList.getFirst();
        } else {
            Stmt hd = stmtList.removeFirst();
            return new CompositionStmt(hd, extract());
        }
    }

    public static Stmt flattenStmt(Stmt s) {
        FlattenStmtListVisitor v = new FlattenStmtListVisitor();
        s.accept(v);
        return v.extract();
    }

    public Void add(Stmt a) {stmtList.addFirst(a); return null; }

    @Override public Void visit(CompositionStmt stmt) {
        stmt.s1.accept(this);
        stmt.s2.accept(this);
        return null;
    }

    @Override
    public Void visit(IfThenElseStmt a) {
        Stmt thenL = flattenStmt(a.thenStmt);
        Stmt elseL = flattenStmt(a.elseStmt);
        return add(new IfThenElseStmt(a.original, a.condition, thenL, elseL));
    }

    @Override public Void visit(AssignmentStmt a) { return add(a); }
    @Override public Void visit(SkipStmt a) { return add(a); }
    @Override public Void visit(SPFCaseStmt c) { return add(c); }
    @Override public Void visit(ArrayLoadInstruction c) { return add(c); }
    @Override public Void visit(ArrayStoreInstruction c) { return add(c); }
    @Override public Void visit(SwitchInstruction c) { return add(c); }
    @Override public Void visit(ReturnInstruction c) { return add(c); }
    @Override public Void visit(GetInstruction c) { return add(c); }
    @Override public Void visit(PutInstruction c) { return add(c); }
    @Override public Void visit(NewInstruction c) { return add(c); }
    @Override public Void visit(InvokeInstruction c) { return add(c); }
    @Override public Void visit(ArrayLengthInstruction c) { return add(c); }
    @Override public Void visit(ThrowInstruction c) { return add(c); }
    @Override public Void visit(CheckCastInstruction c) { return add(c); }
    @Override public Void visit(InstanceOfInstruction c) { return add(c); }
    @Override public Void visit(PhiInstruction c) { return add(c); }
}

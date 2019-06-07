package gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.*;

import static gov.nasa.jpf.symbc.veritesting.ast.def.SkipStmt.skip;


public class ReturnLessVisitor implements AstVisitor<Stmt> {

    @Override
    public Stmt visit(AssignmentStmt a) {
        return new AssignmentStmt(a.lhs, a.rhs);
    }

    @Override
    public Stmt visit(CompositionStmt a) {
        Stmt s1 = a.s1.accept(this);
        Stmt s2 = a.s2.accept(this);

        return new CompositionStmt(s1, s2);
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        Stmt thenStmt = a.thenStmt.accept(this);
        Stmt elseStmt = a.elseStmt.accept(this);
        return new IfThenElseStmt(a.original, a.condition, thenStmt, elseStmt);
    }

    @Override
    public Stmt visit(SkipStmt a) {
        return skip;
    }

    @Override
    public Stmt visit(SPFCaseStmt c) {
        return null;
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        return new ArrayLoadInstruction((SSAArrayLoadInstruction) c.original,c.arrayref, c.index, c.elementType, c.def);
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
        return new ArrayStoreInstruction((SSAArrayStoreInstruction) c.original, c.arrayref, c.index, c.elementType, c.assignExpr);
    }

    @Override
    public Stmt visit(SwitchInstruction c) {
        return null;
    }

    @Override
    public Stmt visit(ReturnInstruction c) {
        return skip;
    }

    @Override
    public Stmt visit(GetInstruction c) {
        return new GetInstruction((SSAGetInstruction) c.original, c.def, c.ref, c.field);
    }

    @Override
    public Stmt visit(PutInstruction c) {
        return new PutInstruction((SSAPutInstruction) c.original, c.def, c.field, c.assignExpr);
    }

    @Override
    public Stmt visit(NewInstruction c) {
        return new NewInstruction((SSANewInstruction) c.original);
    }

    @Override
    public Stmt visit(InvokeInstruction c) {
        return new InvokeInstruction((SSAInvokeInstruction) c.original, c.result, c.params);
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        return new ArrayLengthInstruction((SSAArrayLengthInstruction) c.original, c.arrayref, c.def);
    }

    @Override
    public Stmt visit(ThrowInstruction c) {
        return new ThrowInstruction((SSAThrowInstruction) c.original);
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        return new CheckCastInstruction((SSACheckCastInstruction) c.original, c.result, c.val, c.declaredResultTypes);
    }

    @Override
    public Stmt visit(InstanceOfInstruction c) {
        return new InstanceOfInstruction((SSAInstanceofInstruction) c.original, c.result, c.val, c.checkedType);
    }

    @Override
    public Stmt visit(PhiInstruction c) {
        return new PhiInstruction((SSAPhiInstruction) c.original, c.def, c.rhs);
    }
}

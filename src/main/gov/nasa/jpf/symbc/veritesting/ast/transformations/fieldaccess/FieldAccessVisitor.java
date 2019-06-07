package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

import gov.nasa.jpf.symbc.veritesting.ast.def.GetInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.PutInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.vm.ThreadInfo;

public class FieldAccessVisitor extends AstMapVisitor {
    public FieldAccessVisitor() {
        super(new ExprMapVisitor());
    }

    @Override
    public Stmt visit(GetInstruction c) {
        return super.visit(c);
    }

    @Override
    public Stmt visit(PutInstruction c) {
        return super.visit(c);
    }

    public static DynamicRegion doTransform(ThreadInfo ti, DynamicRegion dynRegion) {

        return dynRegion;
    }
}

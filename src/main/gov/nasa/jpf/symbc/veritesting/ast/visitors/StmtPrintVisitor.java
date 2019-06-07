package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.Ast;

/**
 * Prints out Statement in RangerIR.
 */

public class StmtPrintVisitor extends PrettyPrintVisitor{

    StmtPrintVisitor() {
        super();
    }


    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.SwitchInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ReturnInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.GetInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.PutInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.NewInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.InvokeInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLengthInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLoadInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayStoreInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ThrowInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.CheckCastInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.InstanceOfInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.PhiInstruction c) {
        ind();
        write(c.toString()); nl();
        return null;
    }

    public static String print(Ast s) {
        StmtPrintVisitor visitor = new StmtPrintVisitor();
        s.accept(visitor);
        return visitor.toString();
    }

}

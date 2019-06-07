package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;

/**
 * Pretty print of all statements and expressions in RangerIR.
 */
public class PrettyPrintVisitor implements AstVisitor<Void> {

    int indent = 0;
    private StringBuilder sb = new StringBuilder();
    private String main;

    PrettyPrintExpr ppe;
    ExprVisitorAdapter<Void> eva ;

    protected PrettyPrintVisitor() {
        ppe = new PrettyPrintExpr();
        eva = new ExprVisitorAdapter<Void>(ppe);
    }

    protected void ind() {
        for (int i=0; i < indent; i++) {
            sb.append("   ");
        }
    }

    protected void indent() {
        indent++;
    }

    protected void unindent() {
        if (indent > 0)
            indent--;
    }

    protected void nl() {
        sb.append(System.lineSeparator());
    }

    protected void write(Stmt a) {
        a.accept(this);
    }


    protected void write(String s) {
        sb.append(s);
    }

    protected void write(Expression e) {
        eva.accept(e);
    }

    @Override
    public Void visit(AssignmentStmt a) {
        ind();
        write(a.lhs); write(" := "); write(a.rhs); write("; "); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.CompositionStmt a) {
        write(a.s1);
        write(a.s2);
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt a) {
        ind();
        write("if ("); write(a.condition); write(") {"); nl();
        indent();
        write(a.thenStmt);
        unindent();
        ind(); write("} else {"); nl();
        indent();
        write(a.elseStmt);
        unindent();
        ind(); write("}"); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.SkipStmt a) {
        ind();
        write("skip; "); nl();
        return null;
    }

    @Override
    public Void visit(SPFCaseStmt c) {
        ind();
        write("<SPFCase: cond: "); write(c.spfCondition); write(", reason: "); write(c.reason.toString() + ">"); nl();
        return null;
    }

    // TO DO: print these properly :)
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
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.SwitchInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ReturnInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.GetInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.PutInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.NewInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.InvokeInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLengthInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ThrowInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.CheckCastInstruction c) {
        ind();
        write(c.original.toString()); nl();
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
        write(c.original.toString()); nl();
        return null;
    }


    public class PrettyPrintExpr implements ExprVisitor<Void> {
        @Override
        public Void visit(WalaVarExpr expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(FieldRefVarExpr expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(ArrayRefVarExpr expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(GammaVarExpr expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(AstVarExpr expr) {
            write(expr.toString());
            return null;
        }

        public Void visit(IfThenElseExpr expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(IntConstant expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(IntVariable expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(Operation expr) {
            write("(");
            write(expr.getOperator().toString());
            write(" ");
            for (Expression e: expr.getOperands()) {
                eva.accept(e);
                write(" ");
            }
            // write(expr.toString());
            write(")");
            return null;
        }

        @Override
        public Void visit(RealConstant expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(RealVariable expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(StringConstantGreen expr) {
            write(expr.toString());
            return null;
        }

        @Override
        public Void visit(StringVariable expr) {
            write(expr.toString());
            return null;
        }
    }

    public String toString() {
        return sb.toString();
    }

    public static String print(Ast s) {
        PrettyPrintVisitor visitor = new PrettyPrintVisitor();
        s.accept(visitor);
        return visitor.toString();
    }

    public static String print(Expression s) {
        PrettyPrintVisitor visitor = new PrettyPrintVisitor();
        visitor.eva.accept(s);
        return visitor.toString();
    }
}

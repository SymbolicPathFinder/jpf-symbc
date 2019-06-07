package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.types.FieldReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is PutInstruction in RangerIR that matches the corresponding PutInstruction in Wala and subsequently the corresponding instructions in Java Bytecode.
 */

public class PutInstruction extends Instruction {

    public final Expression def;
    public final FieldReference field;
    public final Expression assignExpr;

    public PutInstruction(SSAPutInstruction ins, Expression ref, FieldReference field, Expression assignExpr) {
        super(ins);
        this.def = ref;
        this.field = field;
        this.assignExpr = assignExpr;
    }

    public PutInstruction(SSAPutInstruction ins) {
        super(ins);
        def = new WalaVarExpr(ins.getRef());
        field = ins.getDeclaredField();
        assignExpr = new WalaVarExpr(ins.isStatic() ? ins.getUse(0) : ins.getUse(1));
    }

    public SSAPutInstruction getOriginal() {
        return (SSAPutInstruction) original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "\n put(" + def + "." + field + ") = " + assignExpr;
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if (!(stmt2 instanceof PutInstruction))
            return false;
        else {
            String def2 = ((PutInstruction) stmt2).def.toString();
            String field2 = ((PutInstruction) stmt2).field.toString();
            String assignExp2 = ((PutInstruction) stmt2).assignExpr.toString();
            return (this.def.toString().equals(def2)
                    && this.field.toString().equals(field2)
                    && this.assignExpr.toString().equals(assignExp2));
        }
    }
}

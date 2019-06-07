package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAReturnInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is ReturnInstruction in RangerIR that matches the corresponding ReturnInstruction in Wala and subsequently the instruction in Java Bytecode.
 */

public class ReturnInstruction extends Instruction {

    public final Expression rhs;

    public ReturnInstruction(SSAReturnInstruction ins, Expression rhs) {
        super(ins);
        this.rhs = rhs;
    }

    public ReturnInstruction(SSAReturnInstruction ins) {
        super(ins);
        rhs = new WalaVarExpr(ins.getUse(0));
    }

    public SSAReturnInstruction getOriginal() {
        return (SSAReturnInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "\n return " + rhs;
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if(!(stmt2 instanceof ReturnInstruction))
            return false;
        else {
            return (this.rhs.toString().equals(((ReturnInstruction) stmt2).rhs.toString()));
        }
    }
}

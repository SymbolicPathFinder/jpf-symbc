package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAThrowInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

/**
 * This is ThrowInstruction in Ranger IR that matches the corresponding ThrowInstruction in Wala and subsequently the instruction in Java Bytecode. This is populated during the transformation of the AST from the CFG, it later disappears upon generating the appropriate SPFCase predicate.
 */

public class ThrowInstruction extends Instruction {

    public ThrowInstruction(SSAThrowInstruction ins) {
        super(ins);
    }

    public SSAThrowInstruction getOriginal() {
        return (SSAThrowInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "Throw Instruction";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        return (stmt2 instanceof ThrowInstruction);
    }
}

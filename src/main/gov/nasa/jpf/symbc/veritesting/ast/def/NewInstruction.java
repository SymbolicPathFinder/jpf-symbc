package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

// TODO: placeholder class: I don't think we need to adequately translate this.


/**
 * This is NewInstruction in Ranger IR that matches the corresponding CheckCastInstruction in Wala and subsequently in Java Bytecode. This is populated through the translation from the CFG to AST and later it will disappear by creating SPFCases.
 */
public class NewInstruction extends Instruction {

    public NewInstruction(SSANewInstruction ins) {
        super(ins);
    }

    public SSANewInstruction getOriginal() {
        return (SSANewInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "new Instruction";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        return (stmt2 instanceof NewInstruction);
    }
}

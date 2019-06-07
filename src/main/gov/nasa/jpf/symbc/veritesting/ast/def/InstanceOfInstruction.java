package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is InstanceOfInstruction in RangerIR that matches the corresponding InstanceOfInstruction in Wala and subsequently the instruction in Java Bytecode.
 */

public class InstanceOfInstruction extends Instruction {

    public final Expression result;
    public final Expression val;
    public final TypeReference checkedType;

    public InstanceOfInstruction(SSAInstanceofInstruction ins, Expression result, Expression val, TypeReference checkedType) {
        super(ins);
        this.result = result;
        this.val = val;
        this.checkedType = checkedType;
    }

    public InstanceOfInstruction(SSAInstanceofInstruction ins) {
        super(ins);
        result = new WalaVarExpr(ins.getDef());
        val = new WalaVarExpr(ins.getUse(0));
        checkedType = ins.getCheckedType();
    }

    public SSAInstanceofInstruction getOriginal() {
        return (SSAInstanceofInstruction) original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "\n" + result + " = " + val + " instanceOf " + checkedType + ")";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if (!(stmt2 instanceof InstanceOfInstruction))
            return false;
        else {
            String result2 = ((InstanceOfInstruction) stmt2).result.toString();
            String val2 = ((InstanceOfInstruction) stmt2).val.toString();
            String checkedType2 = ((InstanceOfInstruction) stmt2).checkedType.toString();

            return (this.result.toString().equals(result2)
                    && this.val.toString().equals(val2)
                    && this.checkedType.toString().equals(checkedType2));
        }
    }
}

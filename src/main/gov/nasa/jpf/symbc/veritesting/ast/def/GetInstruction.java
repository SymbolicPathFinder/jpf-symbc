package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.types.FieldReference;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.FieldSubscriptMap;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is GetInstruction in Ranger IR that matches the corresponding GetInstruction in Wala and subsequently the instruction in Java Bytecode.
 */
public class GetInstruction extends Instruction {

    public final Expression ref;
    public final FieldReference field;
    public final Expression def;
    public FieldSubscriptMap psm = null;

    public GetInstruction(SSAGetInstruction ins, Expression def, Expression ref, FieldReference field) {
        super(ins);
        this.ref = ref;
        this.field = field;
        this.def = def;
    }

    public GetInstruction(SSAGetInstruction ins) {
        super(ins);
        ref = new WalaVarExpr(ins.getRef());
        field = ins.getDeclaredField();
        def = new WalaVarExpr(ins.getDef());
    }

    public SSAGetInstruction getOriginal() {
        return (SSAGetInstruction) original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "\n" + def + " = get(" + ref + "." + field + ")";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if (!(stmt2 instanceof GetInstruction))
            return false;
        else {
            String ref2 = ((GetInstruction) stmt2).ref.toString();
            String field2 = ((GetInstruction) stmt2).field.toString();
            String def2 = ((GetInstruction) stmt2).def.toString();

            boolean psmEqual;
            if ((psm == null) && (((GetInstruction) stmt2).psm == null))
                psmEqual = true;
            else {
                String psm2 = ((GetInstruction) stmt2).psm.toString();
                psmEqual = this.psm.toString().equals(psm2);
            }
            return (psmEqual
                    && (this.ref.toString().equals(ref2))
                    && (this.field.toString().equals(field2))
                    && (this.def.toString().equals(def2))
            );
        }
    }
}

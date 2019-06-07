package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAPhiInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Arrays;


/**
 * This is PhiInstruction in Ranger IR that matches the corresponding PhiInstruction in Wala.
 */
public class PhiInstruction extends Instruction {

    public final Expression def;
    public final Expression [] rhs;

    public PhiInstruction(SSAPhiInstruction ins, Expression def, Expression [] rhs) {
        super(ins);
        this.def = def;
        this.rhs = rhs;
    }

    public PhiInstruction(SSAPhiInstruction ins) {
        super(ins);
        def = new WalaVarExpr(ins.getDef());
        rhs = new Expression[ins.getNumberOfUses()];
        for (int i = 0; i < ins.getNumberOfUses(); i++) {
            rhs[i] = new WalaVarExpr(ins.getUse(i));
        }
    }

    public SSAPhiInstruction getOriginal() {
        return (SSAPhiInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        String rhsStr = new String(rhs[0].toString());
        for(int i=1; i < rhs.length; i++){
            rhsStr += ","+ rhs[i].toString();
        }
        return "\n"+ def + " = phi("+ rhsStr + ")";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if(!(stmt2 instanceof PhiInstruction))
            return false;
        else{
            for(int i =0; i<rhs.length; i++){
                if(!(((PhiInstruction) stmt2).rhs[i].toString().equals(this.rhs[i].toString())))
                    return false;
            }
            return (((PhiInstruction) stmt2).def.toString().equals(this.def.toString()));
        }
    }
}

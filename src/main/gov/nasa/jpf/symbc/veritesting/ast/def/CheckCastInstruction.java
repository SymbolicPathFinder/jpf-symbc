package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Arrays;

/**
 * This is CheckCastInstruction in RangerIR that matches the corresponding CheckCastInstruction in Wala and subsequently the instruction in Java Bytecode.
 */

public class CheckCastInstruction extends Instruction {

    public final Expression result;
    public final Expression val;
    public final TypeReference [] declaredResultTypes;

    public CheckCastInstruction(SSACheckCastInstruction ins, Expression result, Expression val, TypeReference [] declaredResultTypes) {
        super(ins);
        this.result = result;
        this.val = val;
        this.declaredResultTypes = declaredResultTypes;
    }

    public CheckCastInstruction(SSACheckCastInstruction ins) {
        super(ins);
        result = new WalaVarExpr(ins.getDef());
        val = new WalaVarExpr(ins.getUse(0));
        declaredResultTypes = ins.getDeclaredResultTypes();
    }

    public SSACheckCastInstruction getOriginal() {
        return (SSACheckCastInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "\n"+ result + " = checkCast("+ val + "," + Arrays.toString(declaredResultTypes) + ")";
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if (!(stmt2 instanceof CheckCastInstruction))
            return false;
        else{
            String result2 = ((CheckCastInstruction) stmt2).result.toString();
            String val2 = ((CheckCastInstruction) stmt2).val.toString();
            String type2;
            for(int i =0; i< declaredResultTypes.length; i++){
                type2 = ((CheckCastInstruction) stmt2).declaredResultTypes[i].toString();
                if(!this.declaredResultTypes[i].toString().equals(type2))
                    return false;
            }
            return((this.result.toString().equals(result2)) && (this.val.toString().equals(val2)));
        }
    }
}

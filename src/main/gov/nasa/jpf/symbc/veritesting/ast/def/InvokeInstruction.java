package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInvokeInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Arrays;

/**
 * This is InvokeInstruction in RangerIR that matches the corresponding InvokeInstruction in Wala and subsequently the corresponding instructions in Java Bytecode.
 */

public class InvokeInstruction extends Instruction {
    public final Expression[] result;
    public final Expression[] params;

    public InvokeInstruction(SSAInvokeInstruction ins, Expression[] result, Expression[] params) {
        super(ins);
        this.result = result;
        this.params = params;
    }

    public InvokeInstruction(SSAInvokeInstruction ins) {
        super(ins);
        result = new Expression[ins.getNumberOfReturnValues()];
        for (int i = 0; i < ins.getNumberOfReturnValues(); i++) {
            result[i] = new WalaVarExpr(ins.getReturnValue(i));
        }
        this.params = new Expression[ins.getNumberOfParameters()];
        for (int i = 0; i < ins.getNumberOfParameters(); i++) {
            params[i] = new WalaVarExpr(ins.getUse(i));
        }
    }

    public SSAInvokeInstruction getOriginal() {
        return (SSAInvokeInstruction) original;
    }


    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }


    @Override
    public String toString() {
        return "\n" + Arrays.toString(result) + " = invoke " + ((SSAInvokeInstruction) ((InvokeInstruction) this).original).getCallSite().getDeclaredTarget()+ Arrays.toString(params);
    }

    @Override
    public boolean equals(Stmt stmt2) {
        if (!(stmt2 instanceof InvokeInstruction))
            return false;
        else {
                for(int i = 0; i<result.length; i++){
                    if(!((InvokeInstruction) stmt2).result[i].toString().equals(this.result[i].toString()))
                        return false;
                }
            for(int i = 0; i<params.length; i++){
                if(!((InvokeInstruction) stmt2).params[i].toString().equals(this.params[i].toString()))
                    return false;
            }
            return true;
        }
    }
}

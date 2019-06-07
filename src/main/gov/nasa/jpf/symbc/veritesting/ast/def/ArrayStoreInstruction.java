package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is ArrayStoreInstruction in RangerIR that matches the corresponding ArrayStoreInstruction in Wala and subsequently the instruction in Java Bytecode.
 */
public class ArrayStoreInstruction extends Instruction {

    public final Expression arrayref;
    public final Expression index;
    public final TypeReference elementType;
    public final Expression assignExpr;

    public ArrayStoreInstruction(SSAArrayStoreInstruction ins, Expression arrayref, Expression index,
                                 TypeReference elementType, Expression assigned) {
        super(ins);
        this.arrayref = arrayref;
        this.index = index;
        this.elementType = elementType;
        this.assignExpr = assigned;
    }

    public SSAArrayStoreInstruction getOriginal() {
        return (SSAArrayStoreInstruction)original;
    }

    public ArrayStoreInstruction(SSAArrayStoreInstruction ins) {
        super(ins);
        arrayref = new WalaVarExpr(ins.getArrayRef());
        index = new WalaVarExpr(ins.getIndex());
        elementType = ins.getElementType();
        assignExpr = new WalaVarExpr(ins.getValue());
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "" + arrayref + "[" + index+":"+elementType +"] = " + assignExpr;
    }


    @Override
    public boolean equals(Stmt stmt2) {
        if (!(stmt2 instanceof ArrayStoreInstruction))
            return false;
        else {
            String arrayref2 = ((ArrayStoreInstruction) stmt2).arrayref.toString();
            String index2 = ((ArrayStoreInstruction) stmt2).index.toString();
            String elementType2 = ((ArrayStoreInstruction) stmt2).elementType.toString();
            String assignExpr = ((ArrayStoreInstruction) stmt2).assignExpr.toString();

            return ((this.arrayref.toString().equals(arrayref2))
                    && (this.index.toString().equals(index2))
                    && (this.elementType.toString().equals(elementType2))
                    && (this.assignExpr.toString().equals(assignExpr)));
        }
    }
}

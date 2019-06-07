package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

/**
 * A class that carries a fieldReference with a specific SSA subscript.
 */

public final class FieldRefVarExpr extends CloneableVariable {
    public final FieldRef fieldRef;
    public final SubscriptPair subscript;
    public String varId;
    public int uniqueNum = -1;

    public FieldRefVarExpr(FieldRef fieldRef, SubscriptPair subscript) {
        super("@r"+fieldRef.ref + "." + fieldRef.field + "." + subscript);
        this.fieldRef = fieldRef.clone();
        this.subscript = subscript.clone();
    }

    public FieldRefVarExpr(FieldRef fieldRef, SubscriptPair subscript, int uniqueNum) {
        super("@r"+fieldRef.ref + "." + fieldRef.field + "." + subscript);
        this.fieldRef = fieldRef.clone();
        this.subscript = subscript.clone();
        this.uniqueNum = uniqueNum;
    }

    @Override
    public void accept(Visitor visitor) throws VisitorException {
        // will call the Variable entry.
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    @Override

    // I am making class final so that equality works correctly.
    public boolean equals(Object o) {
        if (o instanceof FieldRefVarExpr) {
            FieldRefVarExpr other = (FieldRefVarExpr)o;
            return (this.fieldRef.equals(other.fieldRef) &&
                    this.subscript.equals(other.subscript) && this.uniqueNum == other.uniqueNum);
        }
        return false;
    }

    @Override
    public String toString() {
        return getSymName();
    }

    @Override
    public int getLength() {
        return 1;
    }

    @Override
    public int getLeftLength() {
        return 1;
    }

    @Override
    public int numVar() {
        return 1;
    }

    @Override
    public int numVarLeft() {
        return 1;
    }

    @Override
    public List<String> getOperationVector() {
        return null;
    }

    public String getSymName() {
        String ret = "r" + fieldRef.ref + "." + fieldRef.field + "." + subscript.getSymName();
        if (uniqueNum != -1) ret = ret +  "." + uniqueNum;
        return ret;
    }

    @Override
    public FieldRefVarExpr clone() {
        FieldRefVarExpr ret = null;
        if (uniqueNum != -1) ret = new FieldRefVarExpr(fieldRef.clone(), subscript.clone(), uniqueNum);
        else ret = new FieldRefVarExpr(fieldRef.clone(), subscript.clone());
        return ret;
    }

    @Override
    public FieldRefVarExpr makeUnique(int unique) throws StaticRegionException {
        if (uniqueNum != -1 && unique != uniqueNum) throwException(new StaticRegionException("Attempting to make a already-unique FieldRefVarExpr unique"), INSTANTIATION);
        uniqueNum = unique;
        return this.clone();
    }

    @Override
    public int hashCode() {
        return getSymName().hashCode();
    }
}

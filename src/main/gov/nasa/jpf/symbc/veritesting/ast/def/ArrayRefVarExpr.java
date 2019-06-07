package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

public class ArrayRefVarExpr extends CloneableVariable {
    public final ArrayRef arrayRef;
    public final SubscriptPair subscript;
    public String varId;
    public int uniqueNum = -1;

    public ArrayRefVarExpr(ArrayRef arrayRef, SubscriptPair subscript) {
        super("@r"+arrayRef.ref + "[" + arrayRef.index + "]." + subscript);
        this.arrayRef = arrayRef.clone();
        this.subscript = subscript.clone();
    }

    public ArrayRefVarExpr(ArrayRef arrayRef, SubscriptPair subscript, int uniqueNum) {
        super("@r"+arrayRef.ref + "[" + arrayRef.index + "]." + subscript);
        this.arrayRef = arrayRef.clone();
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
        if (o instanceof ArrayRefVarExpr) {
            ArrayRefVarExpr other = (ArrayRefVarExpr)o;
            return (this.arrayRef.equals(other.arrayRef) &&
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
        String ret = "r" + arrayRef.ref + "[" + arrayRef.index + "]." + subscript.getSymName();
        if (uniqueNum != -1) ret = ret +  "." + uniqueNum;
        return ret;
    }

    @Override
    public ArrayRefVarExpr clone() {
        ArrayRefVarExpr ret;
        if (uniqueNum != -1) ret = new ArrayRefVarExpr(arrayRef.clone(), subscript.clone(), uniqueNum);
        else ret = new ArrayRefVarExpr(arrayRef.clone(), subscript.clone());
        return ret;
    }

    @Override
    public ArrayRefVarExpr makeUnique(int unique) throws StaticRegionException {
        ArrayRefVarExpr retExpr = this.clone();
        if (retExpr.uniqueNum != -1 && unique != retExpr.uniqueNum)
            throwException( new StaticRegionException("Attempting to make a already-unique ArrayRefVarExpr unique"), INSTANTIATION);
        retExpr.uniqueNum = unique;
        if (WalaVarExpr.class.isInstance(retExpr.arrayRef.index))
            assert ((WalaVarExpr)retExpr.arrayRef.index).getSymName().contains("$");
//        if (WalaVarExpr.class.isInstance(arrayRef.index)) {
//            retExpr = new ArrayRefVarExpr(new ArrayRef(arrayRef.ref, getUniqueWalaVarExpr((WalaVarExpr) arrayRef.index, uniqueNum)), subscript, uniqueNum);
//        }
        return retExpr;
    }

    @Override
    public int hashCode() {
        return getSymName().hashCode();
    }
}


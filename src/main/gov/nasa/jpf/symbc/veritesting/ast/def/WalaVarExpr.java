package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

/**
 * This is the class of Wala Variables in RangerIR.
 */
public final class WalaVarExpr extends CloneableVariable {
    /**
     * This number matches the number defined for a specific Wala Variable.
     */
    public final int number;
    private int uniqueNum = -1;

    public WalaVarExpr(int var) {
        super("w" + var);
        this.number = var;
    }


    private WalaVarExpr(int var, int uniqueNum) {
        super("w" + var);
        this.number = var;
        this.uniqueNum = uniqueNum;
    }

    @Override
    public void accept(Visitor visitor) throws VisitorException {
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    @Override
    public boolean equals(Object o) {
        if (o != null && o instanceof WalaVarExpr) {
            WalaVarExpr other = (WalaVarExpr) o;
            return ((this.number == other.number) &&
                    (this.uniqueNum == other.uniqueNum));
        }
        return false;
    }


    /**
     * Gets the symbolic name to be used for vars in SPF.
     *
     * @return retrunds symbolic name, which is the name of the WalaVarExpr, without the @ sign
     */
    public String getSymName() {
        String ret = getName(); //"w" + Integer.toString(number);
        if (uniqueNum != -1)
            ret += "$" + uniqueNum;
        return ret;
    }


    @Override
    public String toString() {
        return getSymName();
    }

    @Override
    public int getLength() {
        return 0;
    }

    @Override
    public int getLeftLength() {
        return 0;
    }

    @Override
    public int numVar() {
        return 0;
    }

    @Override
    public int numVarLeft() {
        return 0;
    }

    @Override
    public List<String> getOperationVector() {
        return null;
    }

    public WalaVarExpr clone() {
        return new WalaVarExpr(number, uniqueNum);
    }

    @Override
    public WalaVarExpr makeUnique(int unique) throws StaticRegionException {
        if (uniqueNum != -1 && unique != uniqueNum)
            throw new StaticRegionException("Attempting to make a already-unique WalaVarExpr unique");
        return new WalaVarExpr(number, unique);
    }

    @Override
    public int hashCode() {
        return getSymName().hashCode();
    }

    public int getUniqueNum() { return uniqueNum; }
/*
    public static WalaVarExpr getUniqueWalaVarExpr(WalaVarExpr expr, int uniqueNum) {
        String varId = Integer.toString(expr.number);
        varId = varId.concat("$");
        varId = varId.concat(Integer.toString(uniqueNum));
        return new WalaVarExpr(expr.number, varId);
    }*/

}
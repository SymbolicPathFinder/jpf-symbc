package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

/** AstVarExpr
 *
    MWW: this is the variable expression for generated local variables.  It
    is currently used in the removeEarlyReturn transformation.

    For now, we do not distinguish between a variable definition and use.
    This is in the spirit of SPF, which also does ot make that distinction.
    However, care must be taken so that we do not declare two variables of
    the same name with different types.
 */

public class AstVarExpr extends CloneableVariable {

    public final String type;
    private int uniqueNum = -1;

    public AstVarExpr(String name, String type)  {
        super(name);
        this.type = type;
        uniqueNum = -1;
    }

    public AstVarExpr(String name, String type, int unique) {
        super(name);
        this.type = type;
        this.uniqueNum = unique;
    }

    @Override
    public void accept(Visitor visitor) throws VisitorException {
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    @Override
    public boolean equals(Object o) {
        if (o == null) { return false; }
        if (o.getClass() != this.getClass()) { return false; }
        AstVarExpr ave = (AstVarExpr)o;
        return (this.getName() == ave.getName() &&
            this.type == ave.type);
    }

    @Override public String toString() {  return this.getSymName(); }
    @Override public int getLength() { return 0; }
    @Override public int getLeftLength() {  return 0; }
    @Override public int numVar() { return 0; }
    @Override public int numVarLeft() { return 0; }
    @Override public List<String> getOperationVector() { return null; }

    @Override
    public CloneableVariable clone() throws CloneNotSupportedException {
        return new AstVarExpr(getName(), this.type, uniqueNum);
    }

    @Override
    public AstVarExpr makeUnique(int unique) throws StaticRegionException {
        if (uniqueNum != -1 && unique != uniqueNum)
            throw new StaticRegionException("Attempting to make a already-unique AstVarExpr unique");
        return new AstVarExpr(this.getName(), this.type, unique);
    }
    public String getSymName() {
        String ret = getName(); //"w" + Integer.toString(number);
        if (uniqueNum != -1)
            ret += "$" + uniqueNum;
        return ret;
    }

    @Override
    public int hashCode() {
        return getSymName().hashCode();
    }

}

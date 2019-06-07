package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

public abstract class CloneableVariable extends Variable implements Cloneable {
    public CloneableVariable(String name) {
        super(name);
    }

    @Override
    public abstract CloneableVariable clone() throws CloneNotSupportedException;

    public abstract CloneableVariable makeUnique(int unique) throws StaticRegionException;

    @Override
    public abstract int hashCode();

    @Override
    public abstract boolean equals(Object obj);
}

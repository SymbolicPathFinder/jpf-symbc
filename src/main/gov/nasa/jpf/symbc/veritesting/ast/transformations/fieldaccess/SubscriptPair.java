package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

public class SubscriptPair {
    public Integer pathSubscript;
    public Integer globalSubscript;

    public SubscriptPair(Integer pathSubscript, Integer globalSubscript) {
        this.pathSubscript = pathSubscript;
        this.globalSubscript = globalSubscript;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof SubscriptPair) {
            SubscriptPair p = (SubscriptPair) obj;
            return pathSubscript.equals(p.pathSubscript) && globalSubscript.equals(p.globalSubscript);
        }
        return false;
    }

    @Override
    public String toString() {
        return pathSubscript.toString() + "." + globalSubscript.toString();
    }

    public String getSymName() {
        return pathSubscript.toString() + "." + globalSubscript.toString();
    }

    @Override
    public SubscriptPair clone() {
        return new SubscriptPair(pathSubscript, globalSubscript);
    }
}

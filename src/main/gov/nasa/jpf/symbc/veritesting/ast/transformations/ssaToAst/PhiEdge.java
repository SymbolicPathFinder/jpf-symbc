package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.ISSABasicBlock;

/**
 * This is used to represent an edge from one block to another in the CFG.
 */
public class PhiEdge {
    public final ISSABasicBlock from;
    public final ISSABasicBlock to;

    public PhiEdge(ISSABasicBlock from, ISSABasicBlock to) {
        this.from = from;
        this.to = to;
    }

    @Override public int hashCode() {
        return 23*from.getNumber() + 31*to.getNumber();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        PhiEdge phiEdge = (PhiEdge) o;

        if (from.getNumber() != phiEdge.from.getNumber()) return false;
        return to.getNumber() == phiEdge.to.getNumber();
    }
}

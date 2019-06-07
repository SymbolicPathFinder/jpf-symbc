package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprBoundaryVisitor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;

public class RegionBoundaryOutput {
    private final ArrayList<Integer> allDefs;
    private final ExprBoundaryVisitor exprVisitor;

    RegionBoundaryOutput(ArrayList<Integer> allDefs, ExprBoundaryVisitor exprBoundaryVisitor) {
        this.allDefs = allDefs;
        this.exprVisitor = exprBoundaryVisitor;
    }

    public Integer getLastDef() {
        if (allDefs.size() > 0)
            return Collections.max(allDefs);
        else
            return null;
    }

    public Integer getFirstDef() {
        if (allDefs.size() > 0)
            return Collections.min(allDefs);
        else
            return null;
    }

    public Integer getFirstUse() {
        return exprVisitor.getFirstUse();
    }

    public Integer getLastUse() {
        return exprVisitor.getLastUse();
    }

    public ArrayList<Integer> getAllDefs() { return allDefs; }

    public HashSet<Integer> getAllUses() { return exprVisitor.getAllUses(); }
}
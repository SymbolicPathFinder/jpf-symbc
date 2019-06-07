package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.InputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;
import java.util.HashSet;

/**
 * An Expression Boundary Visitor that attempts to discover first "use" var inside a region.
 */
public class ExprBoundaryVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    private boolean seenFirstUse = false;
    private Integer firstUse;
    private Integer lastUse;
    private HashSet<Integer> allUses;

    public ExprBoundaryVisitor() { allUses = new HashSet<>(); }

    @Override
    public Expression visit(WalaVarExpr expr) {
        if (expr.number == -1) return expr;
        allUses.add(expr.number);
        if(seenFirstUse){
            if (expr.number < firstUse){
                firstUse = expr.number;
            }
        }
        else{
            firstUse = expr.number;
            lastUse = expr.number;
            seenFirstUse = true;
        }
        if(expr.number > lastUse)
            lastUse = expr.number;
        return expr;
    }

    public Integer getFirstUse() {
        return firstUse;
    }

    public Integer getLastUse() {
        return lastUse;
    }

    public HashSet<Integer> getAllUses() { return allUses; }

}

package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.symbc.veritesting.ast.def.CompositionStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.LinkedHashSet;

public class RegionMetricsVisitor  extends AstMapVisitor {
    private int depth = 0;
    private int maxDepth = 0;
    private long totalNumPaths = 1;
    private long thisNumPaths = 1;
    private LinkedHashSet<Expression> ifCondCache;

    private RegionMetricsVisitor() {
        super(new ExprMapVisitor());
        ifCondCache = new LinkedHashSet<>();
    }

    @Override
    public Stmt visit(CompositionStmt s) {

        thisNumPaths = 1;
        Stmt s1 = s.s1.accept(this);
        long s1NumPaths = thisNumPaths;
        thisNumPaths = 1;
        Stmt s2 = s.s2.accept(this);
        long s2NumPaths = thisNumPaths;
        thisNumPaths = s1NumPaths * s2NumPaths;
        return new CompositionStmt(s1, s2);
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        depth++;
        if (depth > maxDepth) maxDepth = depth;

        long oldNumPaths = thisNumPaths;
        thisNumPaths = 1;
        if (!ifCondCache.contains(a.condition)) {
            ifCondCache.add(a.condition);
            LinkedHashSet<Expression> oldIfCondCache = new LinkedHashSet<>();
            snapshot(oldIfCondCache);
            a.thenStmt.accept(this);
            long thenNumPaths = thisNumPaths;
            thisNumPaths = 1;
            reset(oldIfCondCache);
            a.elseStmt.accept(this);
            reset(oldIfCondCache);
            long elseNumPaths = thisNumPaths;
            thisNumPaths = thenNumPaths + elseNumPaths + oldNumPaths - 1;
        }
        depth--;
        if (depth == 0) totalNumPaths = thisNumPaths;
        return a;
    }

    private void snapshot(LinkedHashSet<Expression> oldIfCondCache) {
        for (Expression e: ifCondCache) { oldIfCondCache.add(e); }
    }

    private void reset(LinkedHashSet<Expression> oldIfCondCache) {
        ifCondCache.clear();
        for (Expression e: oldIfCondCache) { ifCondCache.add(e); }
    }


    public static boolean execute(StaticRegion staticRegion) {
        RegionMetricsVisitor visitor = new RegionMetricsVisitor();
        staticRegion.staticStmt.accept(visitor);
        staticRegion.maxDepth = visitor.maxDepth;
        staticRegion.totalNumPaths = visitor.totalNumPaths;
        return true;
    }

    public static boolean execute(DynamicRegion dynRegion) {
        RegionMetricsVisitor visitor = new RegionMetricsVisitor();
        dynRegion.dynStmt.accept(visitor);
        dynRegion.maxDepth = visitor.maxDepth;
        dynRegion.totalNumPaths = visitor.totalNumPaths;
        return true;
    }
}

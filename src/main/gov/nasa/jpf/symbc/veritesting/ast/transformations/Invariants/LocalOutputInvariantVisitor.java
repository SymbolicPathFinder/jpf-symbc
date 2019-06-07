package gov.nasa.jpf.symbc.veritesting.ast.transformations.Invariants;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.STATIC;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

/* Implements an invariant that checks if the region has up to one stack output */
public class LocalOutputInvariantVisitor extends AstMapVisitor {
    ExprVisitorAdapter<Expression> eva;
    public List<AssignmentStmt> gammaStmts;
    public List<Integer> gammaWalaVarDefs;

    private LocalOutputInvariantVisitor(StaticRegion staticRegion) {
        super(new ExprMapVisitor());
        eva = super.eva;
        gammaStmts = new ArrayList<>();
        gammaWalaVarDefs = new ArrayList<>();
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        if (a.rhs instanceof GammaVarExpr) {
            gammaStmts.add(a);
            if (a.lhs instanceof WalaVarExpr) gammaWalaVarDefs.add(((WalaVarExpr) a.lhs).number);
        }
        return a;
    }

    @Override
    public Stmt visit(CompositionStmt a) {
        a.s1.accept(this);
        a.s2.accept(this);
        return a;
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        a.thenStmt.accept(this);
        a.elseStmt.accept(this);
        gammaStmts.clear();
        return a;
    }

    @Override
    public Stmt visit(SkipStmt a) { return a; }

    @Override
    public Stmt visit(SPFCaseStmt c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ArrayLoadInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ArrayStoreInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(SwitchInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ReturnInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(GetInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(PutInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(NewInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(InvokeInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ArrayLengthInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ThrowInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(CheckCastInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(InstanceOfInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(PhiInstruction c) { gammaStmts.clear(); return c; }

    public static boolean execute(StaticRegion staticRegion) throws StaticRegionException {
        LocalOutputInvariantVisitor visitor = new LocalOutputInvariantVisitor(staticRegion);
        staticRegion.staticStmt.accept(visitor);
        // Every gamma statement's lhs should either be a local output or be the sole stack output of the region
        for (AssignmentStmt assignmentStmt: visitor.gammaStmts) {
            if (assignmentStmt.rhs instanceof GammaVarExpr && WalaVarExpr.class.isInstance(assignmentStmt.lhs)) {
                WalaVarExpr lhs = (WalaVarExpr) assignmentStmt.lhs;
                boolean outputFound = false;
                Set<Integer> outputSlots = staticRegion.outputTable.table.keySet();
                for (int slot : outputSlots) {
                    if (((Integer) staticRegion.outputTable.lookup(slot)) == lhs.number) outputFound = true;
                }
                if (!outputFound) {
                    if (staticRegion.stackOutput == null) staticRegion.stackOutput = lhs;
                    else
                        throwException(new StaticRegionException("static region with gamma expression has more than one stack output in lhs"), STATIC);
                }
            }
        }
        /*
        I (Vaibhav) used to think that this assertion should hold across all multi-path regions. But I found that there
        are three root causes of this assertion's violations that dont result in a correctness violation.
        1. The region summary has a return statement on one side of an if-statement and a local variable assignment on the other.
        2. The local output is not used after the region. For example, this root cause can be seen in
            i. last if-then statement in java.util.Integer.getChars(II[C)V
            ii. the if-then statement containing the innermost if-then-else statement inside the double-nested
                 do-while loop in java.util.Base64$Encoder.encode0([BI[B)I
        3. The local variables that are the outputs go out of scope outside the region and therefore don't need gamma statement.
        Therefore, I am commenting out the below assertion.
         */

        // Every output in the output table should come from a gamma statement
        /*Set<Integer> outputSlots = staticRegion.outputTable.table.keySet();
        for (int slot : outputSlots) {
            if (!visitor.gammaWalaVarDefs.contains(staticRegion.outputTable.lookup(slot)))
                throwException(new StaticRegionException("local output " + staticRegion.outputTable.lookup(slot) +
                        " to stack slot " + slot + " does not have corresponding gamma statement"), STATIC);
        }*/
        return true;
    }
}

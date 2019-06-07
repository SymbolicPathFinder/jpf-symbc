package gov.nasa.jpf.symbc.veritesting.ast.transformations.Invariants;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ForallExprVisitor;
import za.ac.sun.cs.green.expr.*;

import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

/* MWW: Not strictly speaking an AST Invariant because it operates over an
    expression rather than a statement.
 */

/**
 * This class is used to check the invariant that after AstToGreen translation, that the result is a valid Green expression that does not have IfThenElseExpr, WalaVarExpr, FieldRefVarExpr or GammaVarExpr.
 */
public class ValidGreenPredicate extends ForallExprVisitor {

    Map<Class, Integer> failures;

    public void checkInvariant(Expression expr, Map<Class, Integer> failureMap) throws StaticRegionException {
        try {
            eva.accept(expr);
        } catch (IllegalArgumentException e) {
            throwException(new StaticRegionException(e.toString()), INSTANTIATION);
        }
    }

    Boolean incrementFailure(Expression expr) {
        if (failures != null) {
            Class c = expr.getClass();
            if (failures.containsKey(c)) {
                failures.put(c, failures.get(c) + 1);
            } else {
                failures.put(c, 1);
            }
        }
        throwException(new IllegalArgumentException(expr.getClass().toString() + " seen in ValidGreenPredicate!"), INSTANTIATION);
        return null;
    }

    @Override public Boolean visit(IfThenElseExpr expr) { return incrementFailure(expr); }
    @Override public Boolean visit(WalaVarExpr expr) { return incrementFailure(expr); }
    @Override public Boolean visit(FieldRefVarExpr expr) { return incrementFailure(expr); }
    @Override public Boolean visit(GammaVarExpr expr) { return incrementFailure(expr); }
}

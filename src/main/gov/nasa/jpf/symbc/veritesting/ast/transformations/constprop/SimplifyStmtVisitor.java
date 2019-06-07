package gov.nasa.jpf.symbc.veritesting.ast.transformations.constprop;

import com.ibm.wala.types.TypeName;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayExpressions;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.FixedPointAstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;

import java.util.Iterator;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ClassUtils.getType;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.*;
import static za.ac.sun.cs.green.expr.Operation.Operator.EQ;

public class SimplifyStmtVisitor extends FixedPointAstMapVisitor {
    public ExprVisitorAdapter<Expression> eva;
    public DynamicTable<Expression> constantsTable;
    private DynamicRegion dynRegion;

    public SimplifyStmtVisitor(DynamicRegion dynRegion, DynamicTable<Expression> constantsTable) {
        super(new SimplifyRangerExprVisitor(constantsTable));
        eva = super.eva;
        this.constantsTable = constantsTable;
        this.dynRegion = dynRegion;
        this.somethingChanged = false;
    }

    public boolean getSomethingChanged() {
        return ((SimplifyRangerExprVisitor) exprVisitor).somethingChanged;
    }

    public IllegalArgumentException getExprException() {
        IllegalArgumentException ret = null;
        if (((SimplifyRangerExprVisitor) exprVisitor).exception != null) {
            ret = (((SimplifyRangerExprVisitor) exprVisitor).exception);
        }
        return ret;
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        Expression rhs = eva.accept(a.rhs);
        if (isConstant(rhs) || isVariable(rhs)) {
            constantsTable.add((Variable) a.lhs, rhs);
            if (isVariable(rhs)) {
                String type = getGreenVariableType(rhs);
                if (type == null) type = (String) dynRegion.varTypeTable.lookup(rhs);
                if (type == null) type = dynRegion.fieldRefTypeTable.lookup(rhs);
                if (type != null) {
                    if (a.lhs instanceof WalaVarExpr)
                        dynRegion.varTypeTable.add(a.lhs, type);
                    else if (a.lhs instanceof FieldRefVarExpr || a.lhs instanceof ArrayRefVarExpr)
                        dynRegion.fieldRefTypeTable.add((CloneableVariable) a.lhs, type);
                }
            }
            this.somethingChanged = true;
            return SkipStmt.skip;
        }
        return new AssignmentStmt(a.lhs, rhs);
    }

    @Override
    public Stmt visit(IfThenElseStmt c) {
        Expression cond = eva.accept(c.condition);
        ExprUtil.SatResult satResult;
        satResult = isSatGreenExpression(cond);
        if (satResult == ExprUtil.SatResult.FALSE) {
            StatisticManager.ifRemovedCount++;
            this.somethingChanged = true;
            return c.elseStmt.accept(this);
        } else if (satResult == ExprUtil.SatResult.TRUE) {
            this.somethingChanged = true;
            StatisticManager.ifRemovedCount++;
            return c.thenStmt.accept(this);
        } else {
            return new IfThenElseStmt(c.original, cond, c.thenStmt.accept(this), c.elseStmt.accept(this));
        }
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        //TODO: Check if this cast can be done correctly. I (Vaibhav) am assuming it must be correct to get the motivating example to work
        if (c.declaredResultTypes.length != 1)
            throwException(new IllegalArgumentException("Cannot handle checkcast with more than 1 declared result type"), INSTANTIATION);
        TypeName typeName = c.declaredResultTypes[0].getName();
        String type = getType(typeName);
        dynRegion.varTypeTable.add(c.result, type);
        dynRegion.varTypeTable.add(c.val, type);
        Expression rhs = c.val;
        Expression lhs = c.result;
        rhs = eva.accept(rhs);
        if (isConstant(rhs) || isVariable(rhs)) {
            constantsTable.add((Variable) lhs, rhs);
        }
        return new AssignmentStmt(lhs, rhs);
    }

    public static DynamicTable<Expression> makeConstantsTableUnique(DynamicTable<Expression> constantsTable, int uniqueNum) throws StaticRegionException {
        // Alpha-renaming on the constants table
        Iterator<Map.Entry<Variable, Expression>> itr = constantsTable.table.entrySet().iterator();
        DynamicTable<Expression> newConstantsTable = new DynamicTable<>("Constants Table", "Expression", "Constant Value");
        while (itr.hasNext()) {
            Map.Entry<Variable, Expression> entry = itr.next();
            Variable newVar;
            if (entry.getKey() instanceof FieldRefVarExpr) {
                FieldRefVarExpr newExpr = ((FieldRefVarExpr) entry.getKey()).clone();
                newExpr = newExpr.makeUnique(uniqueNum);
                newVar = newExpr;
            } else if (entry.getKey() instanceof ArrayRefVarExpr) {
                ArrayRefVarExpr newExpr = ((ArrayRefVarExpr) entry.getKey()).clone();
                newExpr = newExpr.makeUnique(uniqueNum);
                newVar = newExpr;
            } else if (entry.getKey() instanceof WalaVarExpr) {
                assert ((WalaVarExpr) entry.getKey()).getUniqueNum() != -1;
                newVar = entry.getKey(); // WalaVarExpr are assumed to be alpha-renamed by this point
            } else newVar = entry.getKey();
            newConstantsTable.add(newVar, entry.getValue());
        }
        return newConstantsTable;
    }

    public static SimplifyStmtVisitor create(DynamicRegion dynRegion) {
        DynamicTable<Expression> constantsTable = new DynamicTable<>("Constants Table", "Expression", "Constant Value");
        SimplifyStmtVisitor simplifyVisitor = new SimplifyStmtVisitor(dynRegion, constantsTable);
        return simplifyVisitor;
    }

    public DynamicRegion execute() {
        Stmt simplifiedStmt = dynRegion.dynStmt.accept(this);
        this.instantiatedRegion = new DynamicRegion(dynRegion, simplifiedStmt, dynRegion.spfCaseList, dynRegion.regionSummary,
                dynRegion.spfPredicateSummary, dynRegion.earlyReturnResult);

        if (instantiatedRegion.constantsTable == null)
            instantiatedRegion.constantsTable = this.constantsTable;
        else dynRegion.constantsTable.addAll(this.constantsTable);
//            simplifyArrayOutputs(dynRegion);
        System.out.println("\n--------------- AFTER SIMPLIFICATION ---------------\n");
        System.out.println(StmtPrintVisitor.print(instantiatedRegion.dynStmt));
        Iterator<Map.Entry<Variable, Expression>> itr = instantiatedRegion.constantsTable.table.entrySet().iterator();
        System.out.println("Constants Table:");
        while (itr.hasNext()) {
            Map.Entry<Variable, Expression> entry = itr.next();
            System.out.println(entry.getKey() + ": " + entry.getValue());
        }
        return instantiatedRegion;
    }
}
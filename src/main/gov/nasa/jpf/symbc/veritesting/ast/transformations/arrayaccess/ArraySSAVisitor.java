package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import com.ibm.wala.ssa.SSAThrowInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SPFCaseList;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.FixedPointAstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.*;

import java.util.Arrays;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.compose;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayUtil.getInitialArrayValues;
import static za.ac.sun.cs.green.expr.Operation.Operator.*;

public class ArraySSAVisitor extends FixedPointAstMapVisitor {
    private static int arrayExceptionNumber = 4242  ;
    private DynamicRegion dynRegion;
    private ThreadInfo ti;
    static final int ARRAY_SUBSCRIPT_BASE = 0;
    private GlobalArraySubscriptMap gsm;
    // maps each array to its array of expressions on a path
    public ArrayExpressions arrayExpressions;

    public ArraySSAVisitor(ThreadInfo ti, DynamicRegion dynRegion) {
        super(new ExprMapVisitor());
        this.dynRegion = dynRegion;
        this.ti = ti;
        this.gsm = new GlobalArraySubscriptMap();
        this.arrayExpressions = dynRegion.arrayOutputs != null ? dynRegion.arrayOutputs : new ArrayExpressions(ti);
        somethingChanged = false;
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        if (c.arrayref instanceof IntConstant) {
            int ref = ((IntConstant) c.arrayref).getValue();
            int len = ti.getElementInfo(ref).getArrayFields().arrayLength();
            somethingChanged = true;
            return new AssignmentStmt(c.def, new IntConstant(len));
        } else if (dynRegion.constantsTable != null && c.arrayref instanceof Variable &&
                dynRegion.constantsTable.lookup((Variable) c.arrayref) instanceof IntConstant) {
            int ref = ((IntConstant)dynRegion.constantsTable.lookup((Variable) c.arrayref)).getValue();
            int len = ti.getElementInfo(ref).getArrayFields().arrayLength();
            somethingChanged = true;
            return new AssignmentStmt(c.def, new IntConstant(len));
        } else return c;
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        String exceptionalMessage = null;
        Expression rhs = null;
        String type = null;
        Stmt assignStmt;
        try {
            ArrayRef arrayRef = ArrayRef.makeArrayRef(c);
            if (c.arrayref instanceof IntConstant) {
                if (isUnsupportedArrayRef(arrayRef)) return getThrowInstruction();
                rhs = arrayExpressions.get(arrayRef);
                type = arrayExpressions.getType(arrayRef.ref);
            } else exceptionalMessage = "encountered obj-ref in ArrayLoadInstruction that is not a constant";
            // only one of rhs and exceptionalMessage should be non-null
            assert (rhs == null) ^ (exceptionalMessage == null);
            if (c.def instanceof WalaVarExpr) {
                if (type != null) dynRegion.varTypeTable.add(((WalaVarExpr) c.def).number, type);
            } else exceptionalMessage = "def not instance of WalaVarExpr in GetInstruction: " + c;
            if (exceptionalMessage != null) {
                firstException = new IllegalArgumentException(exceptionalMessage);
                return c;
            } else {
                assignStmt = new AssignmentStmt(c.def, rhs);
                somethingChanged = true;
                return getIfThenElseStmt(arrayRef, assignStmt);
            }
        } catch (IllegalArgumentException e) {
            somethingChanged = false;
            firstException = e;
            return c;
        }
        catch (StaticRegionException e) {
            somethingChanged = false;
            firstException = e;
            return c;
        }
    }

    private Stmt getIfThenElseStmt(ArrayRef arrayRef, Stmt assignStmt) {
        int len = ti.getElementInfo(arrayRef.ref).getArrayFields().arrayLength();
        Expression arrayInBoundsCond = new Operation(AND,
                new Operation(LT, arrayRef.index, new IntConstant(len)),
                new Operation(GE, arrayRef.index, new IntConstant(0)));
        StatisticManager.ArraySPFCaseCount++;
        return new IfThenElseStmt(null, arrayInBoundsCond, assignStmt, getThrowInstruction());
    }

    public static Stmt getThrowInstruction() {
        return new ThrowInstruction(new SSAThrowInstruction(-1, nextArrayExceptionNumber()) {});
    }

    public static int nextArrayExceptionNumber() {
        ++arrayExceptionNumber;
        return arrayExceptionNumber;
    }

    @Override
    public Stmt visit(ArrayStoreInstruction putIns) {
        if (!IntConstant.class.isInstance(putIns.arrayref)) {
            firstException = new IllegalArgumentException("Cannot handle symbolic object references in ArraySSAVisitor");
            return putIns;
        }
        else {
            try {
                ArrayRef arrayRef = ArrayRef.makeArrayRef(putIns);
                if (isUnsupportedArrayRef(arrayRef)) return getThrowInstruction();
                ArrayRefVarExpr arrayRefVarExpr = new ArrayRefVarExpr(arrayRef,
                        new SubscriptPair(-1, gsm.createSubscript(arrayRef.ref)));
                arrayExpressions.update(arrayRef, arrayRefVarExpr);
                Stmt assignStmt = new AssignmentStmt(arrayRefVarExpr, putIns.assignExpr);
                dynRegion.fieldRefTypeTable.add(arrayRefVarExpr.clone(), arrayExpressions.getType(arrayRef.ref));
                somethingChanged = true;
                return getIfThenElseStmt(arrayRef, assignStmt);
            } catch (IllegalArgumentException e) {
                somethingChanged = false;
                firstException = e;
                return putIns;
            }
        }
    }

    private boolean isUnsupportedArrayRef(ArrayRef arrayRef) {
        if (WalaVarExpr.class.isInstance(arrayRef.index))
            if (!dynRegion.varTypeTable.lookup(arrayRef.index).equals("int"))
                return true;
        if (arrayRef.ref == 0) {
            return true;
        }
        return false;
    }

    @Override
    public Stmt visit(IfThenElseStmt stmt) {
        ArrayExpressions oldExps = arrayExpressions.clone();
        Stmt newThen = stmt.thenStmt.accept(this);
        ArrayExpressions thenExps = arrayExpressions.clone();
        arrayExpressions = oldExps.clone();
        Stmt newElse = stmt.elseStmt.accept(this);
        ArrayExpressions elseExps = arrayExpressions.clone();
        arrayExpressions = oldExps.clone();
        Stmt gammaStmt;
        gammaStmt = mergeArrayExpressions(stmt.condition, thenExps, elseExps);
        if (gammaStmt != null) {
            somethingChanged = true;
            return new CompositionStmt(new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse), gammaStmt);
        }
        else return new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse);
    }

    private Stmt mergeArrayExpressions(Expression condition, ArrayExpressions thenExps, ArrayExpressions elseExps) {
        Stmt compStmt = null;
        for (Map.Entry<Integer, Expression[]> entry : thenExps.table.entrySet()) {
            Integer thenArrayRef = entry.getKey();
            String type = thenExps.arrayTypesTable.get(thenArrayRef);
            Expression[] thenExpArr = entry.getValue();
            Expression[] elseExpArr = elseExps.lookup(thenArrayRef);
            if (elseExpArr != null) {
                assert elseExps.arrayTypesTable.get(thenArrayRef).equals(thenExps.arrayTypesTable.get(thenArrayRef));
                assert thenExpArr.length == elseExpArr.length;
                if (!Arrays.equals(thenExpArr, elseExpArr))
                    compStmt = compose(compStmt, createGammaStmtArray(thenArrayRef, condition, thenExpArr, elseExpArr, type), false);
                elseExps.remove(thenArrayRef);
            } else {
                compStmt = compose(compStmt, createGammaStmtArray(thenArrayRef, condition, thenExpArr,
                        getInitialArrayValues(ti, thenArrayRef).getFirst(), type), false);
            }
        }

        for (Map.Entry<Integer, Expression[]> entry : elseExps.table.entrySet()) {
            Integer elseArrayRef = entry.getKey();
            Expression[] elseExpArr = entry.getValue();
            String type = elseExps.arrayTypesTable.get(elseArrayRef);
            if (thenExps.lookup(elseArrayRef) != null) {
                firstException = new IllegalArgumentException("invariant failure: something in elseMap should not be in " +
                        "thenMap at this point");
            } else {
                compStmt = compose(compStmt, createGammaStmtArray(elseArrayRef, condition,
                        getInitialArrayValues(ti, elseArrayRef).getFirst(), elseExpArr, type), false);
            }
        }

        return compStmt;
    }

    private Stmt createGammaStmtArray(int ref, Expression condition, Expression[] thenExpArr, Expression[] elseExpArr,
                                      String type) {
        Stmt compStmt = null;
        for (int i=0; i < thenExpArr.length; i++){
            ArrayRef arrayRef = new ArrayRef(ref, new IntConstant(i));
            ArrayRefVarExpr lhs = new ArrayRefVarExpr(arrayRef,
                    new SubscriptPair(-1, gsm.createSubscript(ref)));
            dynRegion.fieldRefTypeTable.add(lhs, type);
            Stmt assignStmt = new AssignmentStmt(lhs, new GammaVarExpr(condition, thenExpArr[i], elseExpArr[i]));
            compStmt = compose(compStmt, assignStmt, false);
            arrayExpressions.update(arrayRef, lhs);
        }
        return compStmt;
    }



    public DynamicRegion execute(){
        Stmt arrayStmt = dynRegion.dynStmt.accept(this);
        instantiatedRegion = new DynamicRegion(dynRegion, arrayStmt, new SPFCaseList(), null, null, dynRegion.earlyReturnResult);
        instantiatedRegion.arrayOutputs = this.arrayExpressions;
        System.out.println(StmtPrintVisitor.print(instantiatedRegion.dynStmt));
        System.out.println(instantiatedRegion.arrayOutputs);

        return instantiatedRegion;
    }
}

package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAThrowInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SPFCaseList;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.FixedPointAstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.RealVariable;

import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.compose;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.getConstantType;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isConstant;

/*
A Path Subscript Map needs to be passed on from one statement to the other. Each statement updates or uses its PSM.
* A GetInstruction uses the PSM to replace itself with an AssignmentStmt that has a FieldRefVarExpr on the rhs.
* GetInstruction checks if the FieldRef is present in the PSM, if it is, it uses the last subscript to create a new
* FieldRefVarExpr, else it will create a subscript 1.
* A PutInstruction uses the PSM to replace itself with an AssignmentStmt that has a FieldRefVarExpr on the lhs.
PutInstruction checks if the FieldRef is present in the PSM, if it is, it creates a new PSM entry with the subscript
one higher than the last one, else it will create an entry with subscript 2.

This transformation pass should also construct gammas for field writes by merging the PSMs on the then and the else
side of an IfThenElseStmt. For merging the two PSMs, if a FieldRef appeared in both the thenPSM and the elsePSM, we
should create a gamma expression for that FieldRef from its latest subscripts.

The next transformation should do the FieldSubstitution to bring the actual field input values in. It will need to use a
expression visitor that replaces FieldRefVarExpr objects that have subscript 1 with the actual field value.
 */


public class FieldSSAVisitor extends FixedPointAstMapVisitor {
    private static int fieldExceptionNumber=42424242;
    private DynamicRegion dynRegion;
    public FieldSubscriptMap psm;
    private ThreadInfo ti;
    static final int FIELD_SUBSCRIPT_BASE = 0;
    private GlobalSubscriptMap gsm;

    public FieldSSAVisitor(ThreadInfo ti, DynamicRegion dynRegion) {
        super(new ExprMapVisitor());
        this.dynRegion = dynRegion;
        this.psm = dynRegion.psm != null ? dynRegion.psm : new FieldSubscriptMap();
        this.ti = ti;
        this.gsm = new GlobalSubscriptMap();
        this.somethingChanged = false;
    }

    private void populateException(IllegalArgumentException e) {
        this.firstException = e;
    }

    public Stmt bad(Object obj) {
        String name = obj.getClass().getCanonicalName();
//        throwException(new IllegalArgumentException("Unsupported class: " + name +
//                " value: " + obj.toString() + " seen in FieldSSAVisitor"), INSTANTIATION);
        firstException = new IllegalArgumentException("Unsupported class: " + name +
                " value: " + obj.toString() + " seen in FieldSSAVisitor");
        return (Stmt)obj;
    }

    /*public static DynamicRegion execute(ThreadInfo ti, DynamicRegion dynRegion) {
        FieldSSAVisitor visitor = new FieldSSAVisitor(ti, dynRegion);
        Stmt stmt = dynRegion.dynStmt.accept(visitor);
        if (visitor.exception != null) throwException(visitor.exception, INSTANTIATION);
        dynRegion.psm = visitor.psm;
        return new DynamicRegion(dynRegion, stmt, new SPFCaseList(), null, null);
    }*/

    @Override
    public Stmt visit(ReturnInstruction ret) { bad(ret); return ret; }


    @Override
    public Stmt visit(PutInstruction putIns) {
        if (!IntConstant.class.isInstance(putIns.def) && !putIns.getOriginal().isStatic()) {
            populateException(new IllegalArgumentException("Cannot handle symbolic object references in FieldSSAVisitor"));
            return putIns;
        }
        else {
            FieldRef fieldRef;
            try {
                fieldRef = FieldRef.makePutFieldRef(ti, putIns);
            } catch (StaticRegionException e) {
                return getThrowInstruction();
            }
            FieldRefVarExpr fieldRefVarExpr = new FieldRefVarExpr(fieldRef, createSubscript(fieldRef));
            AssignmentStmt assignStmt = new AssignmentStmt(fieldRefVarExpr, putIns.assignExpr);
            String type = null;
            if (WalaVarExpr.class.isInstance(putIns.assignExpr)) {
                if (dynRegion.varTypeTable.lookup(putIns.assignExpr) != null) {
                    type = (String)dynRegion.varTypeTable.lookup(putIns.assignExpr);
                } else {
                    type = new SubstituteGetOutput(ti, fieldRef, true, null).invoke().type;
                }
            } else if (isConstant(putIns.assignExpr)) {
                type = getConstantType(putIns.assignExpr);
            } else if (IntVariable.class.isInstance(putIns.assignExpr)) {
                type = "int";
            } else if (RealVariable.class.isInstance(putIns.assignExpr)) {
                type = "float";
            }
            if (type != null)
                dynRegion.fieldRefTypeTable.add(fieldRefVarExpr.clone(), type);
            somethingChanged = true;
            return assignStmt;
        }
    }

    public static Stmt getThrowInstruction() {
        return new ThrowInstruction(new SSAThrowInstruction(-1, nextFieldExceptionNumber()) {});
    }

    public static int nextFieldExceptionNumber() {
        ++fieldExceptionNumber;
        return fieldExceptionNumber;
    }


    private SubscriptPair createSubscript(FieldRef fieldRef) {
        SubscriptPair subscript = psm.lookup(fieldRef);
        if (subscript == null) {
            subscript = new SubscriptPair(FIELD_SUBSCRIPT_BASE+1, gsm.createSubscript(fieldRef));
            psm.add(fieldRef, subscript);
        } else {
            subscript = new SubscriptPair(subscript.pathSubscript+1, gsm.createSubscript(fieldRef));
            psm.updateValue(fieldRef, subscript);
        }
        return subscript;
    }


    @Override
    public Stmt visit(IfThenElseStmt stmt) {
        FieldSubscriptMap oldMap = psm.clone();
        Stmt newThen = stmt.thenStmt.accept(this);
        FieldSubscriptMap thenMap = psm.clone();
        psm = oldMap.clone();
        Stmt newElse = stmt.elseStmt.accept(this);
        FieldSubscriptMap elseMap = psm.clone();
        psm = oldMap.clone();
        Stmt gammaStmt = mergePSM(stmt.condition, thenMap, elseMap);
        if (gammaStmt != null) {
            somethingChanged = true;
            return new CompositionStmt(new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse), gammaStmt);
        }
        else return new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse);
    }

    private Stmt mergePSM(Expression condition, FieldSubscriptMap thenMap, FieldSubscriptMap elseMap) {
        Stmt compStmt = null;
        for (Map.Entry<FieldRef, SubscriptPair> entry : thenMap.table.entrySet()) {
            FieldRef thenFieldRef = entry.getKey();
            SubscriptPair thenSubscript = entry.getValue();
            SubscriptPair elseSubscript = elseMap.lookup(thenFieldRef);
            if (elseSubscript != null ) {
                if (!thenSubscript.equals(elseSubscript))
                    compStmt = compose(compStmt, createGammaStmt(condition, thenFieldRef, thenSubscript,
                            elseMap.lookup(thenFieldRef)), false);
                elseMap.remove(thenFieldRef);
            } else {
                compStmt = compose(compStmt, createGammaStmt(condition, thenFieldRef, thenSubscript,
                        new SubscriptPair(FIELD_SUBSCRIPT_BASE, gsm.createSubscript(thenFieldRef))), false);
            }
        }

        for (Map.Entry<FieldRef, SubscriptPair> entry : elseMap.table.entrySet()) {
            FieldRef elseFieldRef = entry.getKey();
            SubscriptPair elseSubscript = entry.getValue();
            if (thenMap.lookup(elseFieldRef) != null) {
                throwException(new IllegalArgumentException("invariant failure: something in elseMap should not be in thenMap at this point in FieldSSAVisitor"), INSTANTIATION);
            } else {
                compStmt = compose(compStmt, createGammaStmt(condition, elseFieldRef,
                        new SubscriptPair(FIELD_SUBSCRIPT_BASE, gsm.createSubscript(elseFieldRef)), elseSubscript),
                        false);
            }
        }

        return compStmt;
    }


    private Stmt createGammaStmt(Expression condition, FieldRef fieldRef, SubscriptPair thenSubscript,
                                 SubscriptPair elseSubscript) {
        if (thenSubscript.pathSubscript == FIELD_SUBSCRIPT_BASE && elseSubscript.pathSubscript == FIELD_SUBSCRIPT_BASE) {
            throwException(new IllegalArgumentException("invariant failure: ran into a gamma between subscripts that are both base subscripts in FieldSSAVisitor"), INSTANTIATION);
        }
        SubstituteGetOutput output = new SubstituteGetOutput(ti, fieldRef, true, null).invoke();
        if (output.exceptionalMessage != null) throwException(new IllegalArgumentException(output.exceptionalMessage), INSTANTIATION);
        FieldRefVarExpr fieldRefVarExpr = new FieldRefVarExpr(fieldRef, createSubscript(fieldRef));
        if (output.type != null) {
            dynRegion.fieldRefTypeTable.add(fieldRefVarExpr.clone(), output.type);
        }
        Expression thenExpr = thenSubscript.pathSubscript != FIELD_SUBSCRIPT_BASE ?
                new FieldRefVarExpr(fieldRef, thenSubscript) : output.def;
        Expression elseExpr = elseSubscript.pathSubscript != FIELD_SUBSCRIPT_BASE ?
                new FieldRefVarExpr(fieldRef, elseSubscript) : output.def;
        return new AssignmentStmt(fieldRefVarExpr, new GammaVarExpr(condition, thenExpr, elseExpr));
    }

    /*
    The solution to not have the same FieldRefVarExpr on both sides of a gamma is to map every FieldRef to its
    corresponding (path-specific subscript, global subscript). We should use this global subscript in the
    FieldRefVarExpr. Then when we create gammas, we will be able to create two separate FieldRefVarExpr objects on the
    latest path-specific subscript.
     */
    @Override
    public Stmt visit(GetInstruction c) {
        String exceptionalMessage = null;
        Expression rhs = null;
        String type = null;
        // If we are doing a get field from a constant object reference or if this field access is a static access,
        // we can fill this input in
        if ((c.ref instanceof IntConstant || ((SSAGetInstruction)c.original).isStatic())) {
            FieldRef fieldRef = null;
            try {
                fieldRef = FieldRef.makeGetFieldRef(ti, c);
            } catch (StaticRegionException e) {
                return getThrowInstruction();
            }
            if (psm.lookup(fieldRef) != null) {
                rhs = new FieldRefVarExpr(fieldRef, psm.lookup(fieldRef));
                if (dynRegion.fieldRefTypeTable.lookup(rhs) != null)
                    type = dynRegion.fieldRefTypeTable.lookup(rhs);
            }
            else {
                try {
                    SubstituteGetOutput output = substituteGet(c, fieldRef);
                    type = output.type;
                    rhs = output.def;
                } catch (StaticRegionException e) {
                    exceptionalMessage = e.getMessage();
                }

            }
        } else
            exceptionalMessage = "encountered obj-ref in GetInstruction that is not a constant in FieldSSAVisitor";
        // only one of rhs and exceptionalMessage should be non-null
        assert (rhs == null) ^ (exceptionalMessage == null);
        if (c.def instanceof WalaVarExpr) {
            if (type != null) dynRegion.varTypeTable.add(((WalaVarExpr) c.def).number, type);
        }
        else exceptionalMessage = "def not instance of WalaVarExpr in GetInstruction: " + c + " in FieldSSAVisitor";
        if (exceptionalMessage != null) {
            populateException(new IllegalArgumentException(exceptionalMessage));
            return c;
        }
        else {
            somethingChanged = true;
            return new AssignmentStmt(c.def, rhs);
        }
    }

    private SubstituteGetOutput substituteGet(GetInstruction getIns, FieldRef fieldRef)
            throws StaticRegionException {
        SubstituteGetOutput substituteGetOutput =
                new SubstituteGetOutput(ti, fieldRef, true, null).invoke();
        String exceptionalMessage = substituteGetOutput.getExceptionalMessage();
        Expression def = substituteGetOutput.getDef();
        // only one of def and exceptionalMessage should be non-null
        assert (def == null) ^ (exceptionalMessage == null);
        if (exceptionalMessage != null) throwException(new StaticRegionException(exceptionalMessage), INSTANTIATION);
        return substituteGetOutput;
    }

    public DynamicRegion execute(){
        Stmt fieldStmt = dynRegion.dynStmt.accept(this);

        instantiatedRegion = new DynamicRegion(dynRegion, fieldStmt, new SPFCaseList(), null, null, dynRegion.earlyReturnResult);
        instantiatedRegion.psm = this.psm;

        System.out.println(StmtPrintVisitor.print(instantiatedRegion.dynStmt));

        return instantiatedRegion;
    }


}

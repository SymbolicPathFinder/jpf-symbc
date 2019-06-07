package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.NoSkipVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import gov.nasa.jpf.vm.ArrayFields;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import ia_parser.Exp;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;

import java.util.ArrayList;
import java.util.HashSet;


public class SpfCasesPass1Visitor implements AstVisitor<Stmt> {
    private Expression spfCondition = Operation.TRUE;
    private ThreadInfo ti;
    private ArrayList<SpfCasesInstruction> spfCasesInstructionList;

    public SpfCasesPass1Visitor(ThreadInfo ti, ArrayList spfCasesInstructionList) {
        this.ti = ti;
        if (spfCasesInstructionList == null) { // if null (no SPFCases Instructions is set) assume all possible instructions.
            this.spfCasesInstructionList = new ArrayList<>();
            this.spfCasesInstructionList.add(SpfCasesInstruction.ALL);
        } else
            this.spfCasesInstructionList = spfCasesInstructionList;
        //asserting spfCasesInstructionList has All, then it is a singleton, no other values should exist in the list.
        assert (this.spfCasesInstructionList.contains(SpfCasesInstruction.ALL) ? this.spfCasesInstructionList.size() == 1 : true);
    }


    @Override
    public Stmt visit(AssignmentStmt a) {
        //SH: Dealing with arrays out of bounds here, delayed until we figure out how to do it.
        /*if (!(a.rhs instanceof ArrayRefVarExpr) && !(a.lhs instanceof ArrayRefVarExpr))
            return new AssignmentStmt(a.lhs, a.rhs);

        //case where one of the sides of the assignment is arrayreference.
        Expression arrayCondition = null;
        if ((spfCasesInstructionList.contains(SpfCasesInstruction.ARRAYINSTRUCTION)) || (spfCasesInstructionList.contains(SpfCasesInstruction.ALL))) {
            if (a.rhs instanceof ArrayRefVarExpr) {
                arrayCondition = createArrayCondition((ArrayRefVarExpr) a.rhs);
            } else if (a.lhs instanceof ArrayRefVarExpr) {
                arrayCondition = createArrayCondition((ArrayRefVarExpr) a.lhs);
            }

            Stmt elseStmt = new SPFCaseStmt(Operation.TRUE, SPFCaseStmt.SPFReason.OUT_OF_BOUND_EXCEPTION);

            SSAConditionalBranchInstruction dummy = new SSAConditionalBranchInstruction(-2, null, null, -2, -2, -2);

            assert (arrayCondition != null);
            return new IfThenElseStmt(dummy, arrayCondition, a, elseStmt);
        }*/

        return new AssignmentStmt(a.lhs, a.rhs);
    }

    private Expression createArrayCondition(ArrayRefVarExpr arrayRefVarExpr) {
        int arrayRef = arrayRefVarExpr.arrayRef.ref;
        Expression arrayIndex = arrayRefVarExpr.arrayRef.index;
        ElementInfo ei = ti.getElementInfo(arrayRef);
        int arrayLength = ((ArrayFields) ei.getFields()).arrayLength();
        Expression lowBoundCondition = new Operation(Operation.Operator.GE, arrayIndex, new IntConstant(0));
        Expression upperBoundCondition = new Operation(Operation.Operator.LT, arrayIndex, new IntConstant(arrayLength));
        Expression arrayCcondition = new Operation(Operation.Operator.AND, lowBoundCondition, upperBoundCondition);

        return arrayCcondition;
    }

    @Override
    public Stmt visit(CompositionStmt a) {
        Stmt s1 = a.s1.accept(this);
        Stmt s2 = a.s2.accept(this);
        return new CompositionStmt(s1, s2);
    }

    /**
     * Used to collect the predicate under which an SPFCase needs to occur.
     */
    @Override
    public Stmt visit(IfThenElseStmt a) {
        Stmt s;
        Expression oldSPFCondition = spfCondition;
        spfCondition = new Operation(Operation.Operator.AND, spfCondition, a.condition);
        Stmt thenStmt = a.thenStmt.accept(this);
        spfCondition = new Operation(Operation.Operator.AND, oldSPFCondition, new Operation(Operation.Operator.NOT,  a.condition));
        Stmt elseStmt = a.elseStmt.accept(this);
        s = new IfThenElseStmt(a.original, a.condition, thenStmt, elseStmt);
        spfCondition = oldSPFCondition;
        return s;
    }


    @Override
    public Stmt visit(SkipStmt a) {
        return SkipStmt.skip;
    }

    @Override
    public Stmt visit(SPFCaseStmt c) {
        return c;
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        return new ArrayLoadInstruction(c.getOriginal(), c.arrayref, c.index, c.elementType, c.def);
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
        return new ArrayStoreInstruction(c.getOriginal(), c.arrayref, c.index, c.elementType, c.assignExpr);
    }

    @Override
    public Stmt visit(SwitchInstruction c) {
        return new SwitchInstruction(c.getOriginal());
    }

    @Override
    public Stmt visit(ReturnInstruction c) {
        if (this.spfCasesInstructionList.contains(SpfCasesInstruction.RETURN) ||
                this.spfCasesInstructionList.contains(SpfCasesInstruction.ALL))
            return new SPFCaseStmt(spfCondition,
                    SPFCaseStmt.SPFReason.EARLYRETURN);
        else
            return new ReturnInstruction(c.getOriginal(), c.rhs);
    }

    @Override
    public Stmt visit(GetInstruction c) {
        return new GetInstruction(c.getOriginal(),
                c.def,
                c.ref,
                c.field);
    }

    @Override
    public Stmt visit(PutInstruction c) {
        return new PutInstruction(c.getOriginal(),
                c.def,
                c.field,
                c.assignExpr);
    }

    @Override
    public Stmt visit(NewInstruction c) {
        if (this.spfCasesInstructionList.contains(SpfCasesInstruction.NEWINSTRUCTION) ||
                this.spfCasesInstructionList.contains(SpfCasesInstruction.ALL))
            return new SPFCaseStmt(spfCondition,
                    SPFCaseStmt.SPFReason.OBJECT_CREATION);
        else
            return new NewInstruction(c.getOriginal());
    }

    @Override
    public Stmt visit(InvokeInstruction c) {
        if (this.spfCasesInstructionList.contains(SpfCasesInstruction.INVOKE) ||
                this.spfCasesInstructionList.contains(SpfCasesInstruction.ALL))
            return new SPFCaseStmt(spfCondition,
                    SPFCaseStmt.SPFReason.INVOKE);
        else
            return new InvokeInstruction(c.getOriginal());
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        return new ArrayLengthInstruction(c.getOriginal(), c.arrayref, c.def);
    }

    @Override
    public Stmt visit(ThrowInstruction c) {
        if (this.spfCasesInstructionList.contains(SpfCasesInstruction.THROWINSTRUCTION) ||
                this.spfCasesInstructionList.contains(SpfCasesInstruction.ALL))
            return new SPFCaseStmt(spfCondition,
                    SPFCaseStmt.SPFReason.THROW);
        else
            return new ThrowInstruction(c.getOriginal());
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        return new CheckCastInstruction(c.getOriginal(),
                c.result,
                c.val,
                c.declaredResultTypes);
    }

    @Override
    public Stmt visit(InstanceOfInstruction c) {
        return new InstanceOfInstruction(c.getOriginal(),
                c.result,
                c.val,
                c.checkedType);
    }

    @Override
    public Stmt visit(PhiInstruction c) {
        return new PhiInstruction(c.getOriginal(),
                c.def,
                c.rhs);
    }

    public static DynamicRegion execute(ThreadInfo ti, DynamicRegion dynRegion, ArrayList spfCasesInstructionList) {
        SpfCasesPass1Visitor visitor = new SpfCasesPass1Visitor(ti, spfCasesInstructionList);
        Stmt dynStmt = dynRegion.dynStmt.accept(visitor);


        System.out.println("--------------- SPFCases TRANSFORMATION 1ST PASS ---------------");
        System.out.println(StmtPrintVisitor.print(dynStmt));

        return new DynamicRegion(dynRegion,
                dynStmt,
                new SPFCaseList(), null, null, dynRegion.earlyReturnResult);
    }
}

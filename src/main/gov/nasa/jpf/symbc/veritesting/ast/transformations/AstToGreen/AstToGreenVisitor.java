package gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SimplifyGreenVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import za.ac.sun.cs.green.expr.*;

import java.util.ArrayList;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;


/*
    Preconditions:
        - Only statements are assignment statements and gamma statements

        - All IfThenElse expressions are in "normal form"
            - No IfThenElse/Gamma expressions embedded within expressions other than
              IfThenElse expressions
                e.g.: (if x then y else z) + (if a then b else c)
            - No IfThenElse expressions as conditions of other IfThenElse expressions:
                e.g.: (if (if x then y else z) then a else b)
     */

/**
 * Main visitor that visits all statements and translate them to the appropriate green expression. At the point the expected statements are, assignments, composition and skip.
 */

public class AstToGreenVisitor implements AstVisitor<Expression> {

    public final ArrayList<Expression> greenList = new ArrayList<>();
    public final ArrayList<Stmt> stmtList = new ArrayList<>();

    ExprVisitorAdapter<Expression> eva;
    AstToGreenExprVisitor exprVisitor;


    public AstToGreenVisitor() {
        exprVisitor = new AstToGreenExprVisitor();
        eva = new ExprVisitorAdapter<>(exprVisitor);
    }

    public Expression bad(Object obj) {
        String name = obj.getClass().getCanonicalName();
        throwException(new IllegalArgumentException("Unsupported class: " + name +
                " value: " + obj.toString() + " seen in AstToGreenVisitor"), INSTANTIATION);
        return (Expression)obj;
    }


    public Expression assignStmt(AssignmentStmt stmt) {
        exprVisitor.setAssign(stmt.lhs);
        Expression rhsExp=  eva.accept(stmt.rhs);
        greenList.add(rhsExp);
        stmtList.add(stmt);
        return rhsExp;

    }

    /**
     * Transform a composition statement into a conjunction in green.
     *
     * @param stmt The composition statement to be translated.
     * @return A green expression that represents the compsition statement.
     */
    public Expression compositionStmt(CompositionStmt stmt) {
        Expression lhs = transform(stmt.s1);
        Expression rhs = transform(stmt.s2);
        return new Operation(Operation.Operator.AND, lhs, rhs);
    }

    public Expression transform(Stmt stmt) {
        assert !(stmt instanceof SkipStmt);
        if (stmt instanceof AssignmentStmt) {
            return assignStmt((AssignmentStmt) stmt);
        } else if (stmt instanceof CompositionStmt) {
            return compositionStmt((CompositionStmt) stmt);
        } else {
            return bad(stmt);
        }
    }

    @Override
    public Expression visit(SkipStmt a) {
        return Operation.TRUE;
    }

    @Override
    public Expression visit(AssignmentStmt a) {
        return assignStmt(a);
    }

    @Override
    public Expression visit(CompositionStmt a) {
        return compositionStmt(a);
    }

    @Override
    public Expression visit(IfThenElseStmt a) {
        return bad(a);
    }

    @Override
    public Expression visit(SPFCaseStmt c) {
        return bad(c);
    }

    @Override
    public Expression visit(ArrayLoadInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(ArrayStoreInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(SwitchInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(ReturnInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(GetInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(PutInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(NewInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(InvokeInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(ArrayLengthInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(ThrowInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(CheckCastInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(InstanceOfInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(PhiInstruction c) {
        return bad(c);
    }

    public static DynamicRegion execute(DynamicRegion dynRegion) throws VisitorException {

        WalaVarToSPFVarVisitor walaVarVisitor = new WalaVarToSPFVarVisitor(dynRegion.varTypeTable);
        AstMapVisitor astMapVisitor = new AstMapVisitor(walaVarVisitor);
        Stmt noWalaVarStmt = dynRegion.dynStmt.accept(astMapVisitor);
        FieldArrayVarToSPFVarVisitor fieldRefVisitor = new FieldArrayVarToSPFVarVisitor(dynRegion.fieldRefTypeTable);
        astMapVisitor = new AstMapVisitor(fieldRefVisitor);
        Stmt noRangerVarStmt = noWalaVarStmt.accept(astMapVisitor);
        NoSkipVisitor noSkipVisitor = new NoSkipVisitor();

        System.out.println("\n--------------- NO-SKIP OPTIMIZATION ---------------");
        Stmt noSkipStmt = noRangerVarStmt.accept(noSkipVisitor);
//        if (noSkipStmt instanceof SkipStmt)
//            throwException(new IllegalArgumentException("concrete region"), INSTANTIATION);
        System.out.println(PrettyPrintVisitor.print(noSkipStmt));

        System.out.println("\n--------------- TO GREEN TRANSFORMATION ---------------");
        AstToGreenVisitor toGreenVisitor = new AstToGreenVisitor();
        Expression regionSummary = noSkipStmt.accept(toGreenVisitor);


        System.out.format("%1$-70s %2$-100s\n", "|Stmt", "|Green Expression");
        System.out.format("%1$-70s %2$-100s\n", "|-----------------------------------------------------------",
                "|------------------------------------------------------");

        for (int i = 0; i < toGreenVisitor.stmtList.size(); i++) {
            System.out.format("%1$-70s %2$-100s\n", toGreenVisitor.stmtList.get(i), ExprUtil.AstToString(toGreenVisitor.greenList.get(i)));
        }

        System.out.println("\nGreen Expression pushed on the Path Condition:");
        System.out.println(ExprUtil.AstToString(regionSummary));
        System.out.println("Stack output: " + dynRegion.stackOutput);

/*


        SimplifyGreenVisitor simplifyVisitor = new SimplifyGreenVisitor();
        regionSummary.accept(simplifyVisitor);

        Expression simpleRegionSummary = simplifyVisitor.returnExp;

        System.out.println("\nSimplified region Summary is:");
        System.out.println(ExprUtil.AstToString(simpleRegionSummary));
*/


        DynamicRegion greenDynRegion = new DynamicRegion(dynRegion,
                dynRegion.dynStmt,
                dynRegion.spfCaseList,
                regionSummary,
                null,
                dynRegion.earlyReturnResult);

        return greenDynRegion;
    }
}

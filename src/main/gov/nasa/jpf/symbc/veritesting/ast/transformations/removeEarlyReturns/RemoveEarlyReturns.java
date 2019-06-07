package gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns;

import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprIdVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import ia_parser.Exp;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

import java.util.Deque;
import java.util.LinkedList;

/**
 * This class removes early return statements.
 * <p>
 * Algorithm: moving from innermost to outermost.
 * <p>
 * If
 */
public class RemoveEarlyReturns {

    StaticRegion region;

    public class ReturnResult {
        public final Stmt stmt;
        public final Expression assign;
        public Expression condition;
        public final Pair<Integer, String> retPosAndType;
        public Expression retVar;

        public ReturnResult(Stmt stmt, Expression assign, Expression condition, Pair<Integer, String> retPosAndType, Expression retVar) {
            this.stmt = stmt;
            this.assign = assign;
            this.condition = condition;
            this.retPosAndType = retPosAndType;
            this.retVar = retVar;
        }

        public ReturnResult(Stmt stmt) {
            this.stmt = stmt;
            this.assign = null;
            this.condition = null;
            this.retPosAndType = null;
        }

        public ReturnResult(Stmt stmt, ReturnResult res) {
            this.stmt = stmt;
            this.assign = res.assign;
            this.condition = res.condition;
            this.retPosAndType = res.retPosAndType;
            this.retVar = res.retVar;

        }

        public final boolean isNull() {
            return this.condition == null;
        }

        public final boolean hasER() {
            return !isNull();
        }

        public final boolean isTrue() {
            return !isNull() && Operation.TRUE.equals(this.condition);
        }

    }

    // Don't transform expressions
    private static final ExprIdVisitor exprVisitor = new ExprIdVisitor();
    private Deque<Expression> conditionList = new LinkedList<>();

    public RemoveEarlyReturns() {
    }

    public RemoveEarlyReturns(StaticRegion region) {
        this.region = region;
    }

    // Unfortunately this is like 10x longer than in ML or probably Scala.
    public ReturnResult doStmt(ReturnResult init) throws InvalidClassFileException {

        ReturnResult newResult;
        if (init.isTrue()) {
            newResult = new ReturnResult(SkipStmt.skip, init);
            return newResult;
        } else if (init.stmt instanceof ReturnInstruction) {
            ReturnInstruction returnInstruction = (ReturnInstruction) init.stmt;
            int returnPosition = ((IBytecodeMethod) (region.ir.getMethod())).getBytecodeIndex(returnInstruction.original.iindex);
            String returnType = region.varTypeTable.lookup(returnInstruction.original.getUse(0));
            Expression assign;
            if (init.hasER()) {
                assign = new IfThenElseExpr(init.condition, init.assign,
                        returnInstruction.rhs);
            } else {
                assign = returnInstruction.rhs;
            }
            /*if (region.isMethodRegion)//return no return statements
                newResult = new ReturnResult(SkipStmt.skip, assign,
                        Operation.TRUE, new Pair(returnPosition, returnType), null);
            else //leave return statements.
                newResult = new ReturnResult(init.stmt, assign,
                        Operation.TRUE, new Pair(returnPosition, returnType), null);*/
            newResult = new ReturnResult(SkipStmt.skip, assign,
                    Operation.TRUE, new Pair(returnPosition, returnType), null);
            return newResult;
        } else if (init.stmt instanceof IfThenElseStmt) {
            Expression innerAssign;
            Expression innerCondition;
            Stmt resultStmt;
            Pair<Integer, String> retPosAndType;

            IfThenElseStmt ifThenElseStmt = (IfThenElseStmt) init.stmt;
            ReturnResult thenResult = doStmt(
                    new ReturnResult(ifThenElseStmt.thenStmt));
            ReturnResult elseResult = doStmt(
                    new ReturnResult(ifThenElseStmt.elseStmt));

            if (thenResult.hasER() && elseResult.hasER()) {
                innerAssign = new IfThenElseExpr(
                        new Operation(Operation.Operator.AND,
                                ifThenElseStmt.condition,
                                thenResult.condition),
                        thenResult.assign,
                        elseResult.assign);
                if (thenResult.isTrue() && elseResult.isTrue()) {
                    innerCondition = Operation.TRUE;
                    resultStmt = SkipStmt.skip;
                } else {
                    innerCondition = new IfThenElseExpr(
                            ifThenElseStmt.condition,
                            thenResult.condition,
                            elseResult.condition);
                    resultStmt = new IfThenElseStmt(
                            null,
                            ifThenElseStmt.condition,
                            thenResult.stmt,
                            elseResult.stmt);
                }
                retPosAndType = thenResult.retPosAndType;
            } else if (thenResult.hasER()) {
                innerAssign = thenResult.assign;
                innerCondition = new Operation(Operation.Operator.AND,
                        ifThenElseStmt.condition,
                        thenResult.condition);
                resultStmt = new IfThenElseStmt(
                        null,
                        ifThenElseStmt.condition,
                        thenResult.stmt,
                        elseResult.stmt);
                retPosAndType = thenResult.retPosAndType;
            } else if (elseResult.hasER()) {
                innerAssign = elseResult.assign;
                innerCondition = new Operation(Operation.Operator.AND,
                        ifThenElseStmt.condition,
                        elseResult.condition);
                resultStmt = new IfThenElseStmt(
                        null,
                        ifThenElseStmt.condition,
                        thenResult.stmt,
                        elseResult.stmt);
                retPosAndType = elseResult.retPosAndType;
            } else {
                resultStmt = init.stmt;
                innerAssign = null;
                innerCondition = null;
                retPosAndType = null;
            }

            if (init.hasER() && innerAssign != null) {
                newResult = new ReturnResult(
                        resultStmt,
                        new IfThenElseExpr(init.condition, init.assign, innerAssign),
                        new Operation(Operation.Operator.OR,
                                init.condition, innerCondition), init.retPosAndType, null);
            } else if (init.hasER()) {
                newResult = new ReturnResult(resultStmt, init);
            } else if (innerAssign != null) {
                newResult = new ReturnResult(resultStmt, innerAssign, innerCondition, retPosAndType, null);
            } else {
                newResult = new ReturnResult(resultStmt);
            }
            return newResult;
        } else if (init.stmt instanceof CompositionStmt) {
            CompositionStmt cStmt = (CompositionStmt) init.stmt;
            ReturnResult newResult1 = doStmt(new ReturnResult(cStmt.s1, init));
            ReturnResult newResult2 = doStmt(new ReturnResult(cStmt.s2, newResult1));
            Stmt stmt;
            if (newResult1.stmt instanceof SkipStmt) {
                stmt = newResult2.stmt;
            } else if (newResult2.stmt instanceof SkipStmt) {
                stmt = newResult1.stmt;
            } else {
                stmt = new CompositionStmt(newResult1.stmt, newResult2.stmt);
            }
            newResult = new ReturnResult(stmt, newResult2);
            return newResult;
        } else {
            // do nothing!
            return init;
        }
    }

    /*
Do_Stmt(stmt, assign, condition):

  If (condition == “true”)
     return (Skip, assign, condition);

  Case stmt of:
     return X:
        If (assign != null)
            assign = if (condition) then assign else X);
        Else
            assign = X;
        condition = true;
        stmt = skip;
        break;

     If c then t else e:
        (TS, TC, TE) = Do_Stmt(t, null, null);
        (ES, EC, EE) = Do_Stmt(e, null, null);
        // Inner condition…
        if (TE != null && EE != null) {
           inner_e = if (TC) then TE else EE
           inner_c = (if TC == “true” and EE == “true” then “true” else (if c then TC else EC));
           stmt = If (inner_c == “true”) then Skip else
              If (c) then TS else TE;
        } else if (TE != null) {
           inner_e = TE;
           inner_c = c && TC;
           stmt = if (c) then TS else TE;
        } else if (EE != null) {
           inner_e = EE;
           inner_c = !c && EC;
           stmt = if (c) then TS else TE;
        } else {
           inner_e = null;
           inner_c = null;             stmt = if (c) then TS else TE;
        }
        If (inner_e) {
           assign = if (condition) then assign else inner_e;
           condition = if (inner_c == “true”) then “true” else (condition || inner_c);
        }
        Break;

     S1; S2:
        (S1, Assign, condition) := Do_Stmt(S1, assign, condition);
        (S2, Assign, condition) := Do_Stmt(S2, assign, condition);
        stmt =
           if (S1 == Skip) S2 else if (S2 == Skip) then S1 else S1; S2;
        Break;

     Default:
        // do nothing.

    Return (stmt, assign, condition);

// yay!
// Questions:
// It would probably be best to leave these as assignments at the end of the block,
// Then simply reference these variables as the “special” variables within the block.
// so…good - this means that the new variable stuff I created is worthwhile.
// Also, preserves SSA, as there is only one variable for each.

Similar things can be done for SPF Cases.

 */

    public StaticRegion analyze(StaticRegion region) throws StaticRegionException, InvalidClassFileException {
        System.out.println("\nRegion prior to removeEarlyReturns: " +
                PrettyPrintVisitor.print(region.staticStmt));
        ReturnResult stmtResult = doStmt(new ReturnResult(region.staticStmt));
        Stmt resultStmt;
        if (stmtResult.hasER()) { // if the region has a early return
            Expression assignVarExpr = new AstVarExpr("~earlyReturnResult", stmtResult.retPosAndType.getSecond());
            AstVarExpr erOccurredExpr = new AstVarExpr("~earlyReturnOccurred", "BOOL");

            stmtResult.retVar = assignVarExpr;
            Stmt returnLessOrNotStmt;

            if (region.isMethodRegion) {
                ReturnLessVisitor returnLessVisitor = new ReturnLessVisitor();
                returnLessOrNotStmt = region.staticStmt.accept(returnLessVisitor);
            } else
                returnLessOrNotStmt = region.staticStmt;

            resultStmt =
                    new CompositionStmt(returnLessOrNotStmt,
                            new AssignmentStmt(assignVarExpr, stmtResult.assign));

            /*
            resultStmt =
                    new CompositionStmt(returnLessStmt,
                            new CompositionStmt(
                                    new AssignmentStmt(assignVarExpr, stmtResult.assign),
                                    new AssignmentStmt(erOccurredExpr, stmtResult.condition)));*/

        } else // if no early return was found, then just propagate the stmt.
            resultStmt = stmtResult.stmt;


        System.out.println("\nRegion after removeEarlyReturns: " +
                StmtPrintVisitor.print(resultStmt));
        // VarTypeTable varTypeTable = new VarTypeTable(region.varTypeTable);

        // MWW TODO: need to add in types and new vars somewhere.
        // MWW TODO: Current type table is from integers; this is not the way to do it.
        //    StaticRegion resultRegion = new StaticRegion(resultStmt, region.ir, region.isMethodRegion, region.endIns, null, stmtResult);
        StaticRegion resultRegion = new StaticRegion(resultStmt, region, stmtResult);
        return resultRegion;
    }

    public static StaticRegion removeEarlyReturns(StaticRegion region) throws StaticRegionException, InvalidClassFileException {
        RemoveEarlyReturns rer = new RemoveEarlyReturns(region);
        StaticRegion result = rer.analyze(region);
        return result;
    }

}

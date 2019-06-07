package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns.RemoveEarlyReturns;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import ia_parser.Exp;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.constprop.SimplifyStmtVisitor.makeConstantsTableUnique;

/**
 * Unique region creator, of both conditional regions and method regions.
 */

public class UniqueRegion {

    /**
     * Used to create a unique conditional region.
     *
     * @param staticRegion Dynamic region that needs to be unique.
     * @return A new static region that is unique.
     */

    public static DynamicRegion execute(StaticRegion staticRegion) throws CloneNotSupportedException, StaticRegionException {

        ++DynamicRegion.uniqueCounter;
        int uniqueNum = DynamicRegion.uniqueCounter;
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(uniqueNum);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);

        Stmt dynStmt = staticRegion.staticStmt.accept(stmtVisitor);
        RemoveEarlyReturns.ReturnResult oldEarlyReturn = staticRegion.earlyReturnResult;
        DynamicRegion dynRegion;
        if (oldEarlyReturn.hasER()) { //make early return result (assign and condition) unique as well.
            ExprVisitorAdapter eva = new ExprVisitorAdapter(expUniqueVisitor);
            Expression newAssign = (Expression) eva.accept(oldEarlyReturn.assign);
            Expression newCondition = (Expression) eva.accept(oldEarlyReturn.condition);
            Expression newRetVar = (Expression) eva.accept(oldEarlyReturn.retVar);

            RemoveEarlyReturns o = new RemoveEarlyReturns();
            RemoveEarlyReturns.ReturnResult newReturnResult = o.new ReturnResult(oldEarlyReturn.stmt, newAssign, newCondition, oldEarlyReturn.retPosAndType, newRetVar);
            dynRegion = new DynamicRegion(staticRegion,
                    dynStmt,
                    uniqueNum, newReturnResult);
        }else
            dynRegion = new DynamicRegion(staticRegion,
                    dynStmt,
                    uniqueNum, staticRegion.earlyReturnResult);


        System.out.println("\n--------------- UNIQUENESS TRANSFORMATION ---------------");
        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
        dynRegion.slotParamTable.print();
        dynRegion.inputTable.print();
        dynRegion.varTypeTable.print();
        dynRegion.outputTable.print();
        System.out.println("Stack output: " + dynRegion.stackOutput);

        return dynRegion;
    }

    public static DynamicRegion execute(DynamicRegion oldDynRegion) throws StaticRegionException, CloneNotSupportedException {
        int uniqueNum = DynamicRegion.uniqueCounter;
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(uniqueNum);
        if (expUniqueVisitor.sre != null) throwException(expUniqueVisitor.sre, INSTANTIATION);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);

        Stmt dynStmt = oldDynRegion.dynStmt.accept(stmtVisitor);

        DynamicRegion newDynRegion = new DynamicRegion(oldDynRegion,
                dynStmt,
                oldDynRegion.spfCaseList, oldDynRegion.regionSummary, oldDynRegion.spfPredicateSummary, oldDynRegion.earlyReturnResult);
        newDynRegion.fieldRefTypeTable.makeUniqueKey(uniqueNum);
        newDynRegion.psm.setUniqueNum(uniqueNum);
        newDynRegion.arrayOutputs = newDynRegion.arrayOutputs.makeUnique(uniqueNum);
        if (oldDynRegion.stackOutput != null)
            newDynRegion.stackOutput = oldDynRegion.stackOutput.makeUnique(uniqueNum);


        if(VeritestingListener.simplify)
            newDynRegion.constantsTable = makeConstantsTableUnique(newDynRegion.constantsTable, uniqueNum);

        return newDynRegion;
    }

}

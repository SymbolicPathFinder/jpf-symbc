package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.AstVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SPFCaseList;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayExpressions;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArraySubscriptMap;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.FieldSubscriptMap;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns.RemoveEarlyReturns;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;

import java.util.Iterator;
import java.util.Map;

/**
 * This class represents a DynamicRegion, that is, a StaticRegion that has been processed dynamically, this is done initially through uniquness transformation then later with the substitution and other transformations.
 * A main difference in this data structure than the StaticRegion is that, the dynamic region now holds environment tables that have a unique name for every variable used.
 */
public class DynamicRegion implements Region {
    /**
     * unique counter used to maintain uniqueness among vars in case a region was used multiple times, like in a loop.
     */
    public static int uniqueCounter = 0;

    /**
     * A statement that represents the region after instantiation.
     */
    public final Stmt dynStmt;

    /**
     * A table that holds the mapping of vars in the dynamic statement to their corresponding stack slot.
     */
    public final DynamicTable slotParamTable;


    /**
     * A table that holds inputs to the region.
     */
    public final DynamicTable inputTable;

    /**
     * An environment able that holds the vars that needs to be populate their summarized output to SPF.
     */
    public final DynamicOutputTable outputTable;

    /**
     * This holds the static version of the region that is matching this instantiation.
     */
    public final IR ir;

    /**
     * An environment table that holds the types of all Wala vars in the region.
     */
    public final DynamicTable varTypeTable;

    /**
     * Holds the total number of IfThenElseStmts present in this static region
     */
    public int maxDepth = -1;

    /**
     * Holds the total number of execution paths that can be taken through this region
     */
    public long totalNumPaths = -1;


    /**
     * An environment table that holds the types of all field variables, referenced by FieldRefVarExpr objects, in the region.
     * This table also holds the types of all array references, referenced by ArrayRefVarExpr objects, in the region.
     */
    public final FieldRefTypeTable fieldRefTypeTable;

    /**
     * Holds path subscript map for field references in the region
     */
    public FieldSubscriptMap psm;

    /**
     * Identifies the End Position that the region is summarizing and which also SPF to resume from.
     */
    public final int endIns;

    /**
     * Identifies if the dynamic region corresponds to a region that starts with a condition, or is it enclosing the summary of the whole method.
     */
    public final boolean isMethodRegion;

    /**
     * Holds all SPFCases predicates that are not statically summarized and are left for SPF to explore.
     */
    public final SPFCaseList spfCaseList;

    /**
     * This holds the region greeen expression after all transformations are done.
     */
    public final Expression regionSummary;

    /**
     * This carries the green expression under which partial evaluation will be done with SPF.
     */
    public final Expression spfPredicateSummary;

    /**
     * Holds output expressions to be written into arrays
     */
    public ArrayExpressions arrayOutputs;

    /*
    * Holds all variables in the region summary that were found to be constants
     */
    public DynamicTable<Expression> constantsTable;


    public RemoveEarlyReturns.ReturnResult earlyReturnResult;

    /**
     * Holds the expression that should be written out to the stack
     */
    public WalaVarExpr stackOutput = null;

    public DynamicRegion(DynamicRegion oldDynRegion,
                         Stmt dynStmt,
                         SPFCaseList spfCaseList,
                         Expression regionSummary,
                         Expression spfRegionSummary,
                         RemoveEarlyReturns.ReturnResult earlyReturnResult) {
        this.ir = oldDynRegion.ir;
        this.dynStmt = dynStmt;
       /* this.inputTable = new DynamicTable(
                "Region Input Table",
                "var",
                oldDynRegion.isMethodRegion ? "param" : "slot");
*/

        this.inputTable = oldDynRegion.inputTable;
        this.endIns = oldDynRegion.endIns;
        this.isMethodRegion = oldDynRegion.isMethodRegion;
        this.outputTable = oldDynRegion.outputTable;
        this.varTypeTable = oldDynRegion.varTypeTable;
        this.slotParamTable = oldDynRegion.slotParamTable;
        this.spfCaseList = spfCaseList;
        this.regionSummary = regionSummary;
        this.spfPredicateSummary = spfRegionSummary;
        this.fieldRefTypeTable = oldDynRegion.fieldRefTypeTable;
        this.psm = oldDynRegion.psm;
        this.earlyReturnResult = earlyReturnResult;
        this.arrayOutputs = oldDynRegion.arrayOutputs;
        this.constantsTable = oldDynRegion.constantsTable;
        this.stackOutput = oldDynRegion.stackOutput;
        this.totalNumPaths = oldDynRegion.totalNumPaths;
        this.maxDepth = oldDynRegion.maxDepth;
    }


    /**
     * Constructor that is used to create a dynamic region out of a static region.
     *
     * @param staticRegion
     * @param dynStmt
     * @param uniqueNum
     */

    public DynamicRegion(StaticRegion staticRegion, Stmt dynStmt, int uniqueNum, RemoveEarlyReturns.ReturnResult returnResult) throws StaticRegionException, CloneNotSupportedException {
        this.ir = staticRegion.ir;
        this.dynStmt = dynStmt;
        this.endIns = staticRegion.endIns;
        this.isMethodRegion = staticRegion.isMethodRegion;
        this.spfCaseList = new SPFCaseList();
        this.regionSummary = null;
        this.spfPredicateSummary = null;
        this.earlyReturnResult = returnResult;

        this.slotParamTable = new DynamicTable(
                (StaticTable) staticRegion.slotParamTable, uniqueNum);

        this.inputTable = new DynamicTable(
                (StaticTable) staticRegion.inputTable,
                uniqueNum);

        this.varTypeTable = new DynamicTable(
                (StaticTable) staticRegion.varTypeTable,
                uniqueNum);
        if(earlyReturnResult.hasER()){
            //AstVarExpr earlyReturnVar = new AstVarExpr( "~earlyReturnResult", earlyReturnResult.retPosAndType.getSecond());
            assert(earlyReturnResult.retVar instanceof AstVarExpr);
            this.varTypeTable.add(((AstVarExpr)earlyReturnResult.retVar).makeUnique(uniqueNum), earlyReturnResult.retPosAndType.getSecond());
        }
        this.outputTable = new DynamicOutputTable(
                (OutputTable) staticRegion.outputTable, uniqueNum);
        this.fieldRefTypeTable = new FieldRefTypeTable();
        this.psm = new FieldSubscriptMap();
        this.arrayOutputs = null;
        this.constantsTable = null;
        this.stackOutput = staticRegion.stackOutput;
    }

}

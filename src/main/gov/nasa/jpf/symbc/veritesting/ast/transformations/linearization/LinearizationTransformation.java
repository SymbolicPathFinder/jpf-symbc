package gov.nasa.jpf.symbc.veritesting.ast.transformations.linearization;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.DefaultTransformation;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;

/**
 * Basic class that invokes Linearization transformation, by removing any if statement, and leaving only its "then" and "else" statements. It returns a new region that has been linearized.
 */
public class LinearizationTransformation extends DefaultTransformation {

    @Override
    public DynamicRegion execute(DynamicRegion region) {
        System.out.println("\n--------------- LINEARIZATION TRANSFORMATION ---------------");

        LinearizationVisitor v = new LinearizationVisitor();
        Stmt stmt = region.dynStmt.accept(v);

        System.out.println(StmtPrintVisitor.print(stmt));
        System.out.println("\nStack output: " + region.stackOutput);

        return new DynamicRegion(region,
                stmt, region.spfCaseList, null,null, region.earlyReturnResult);
    }
}

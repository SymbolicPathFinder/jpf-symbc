package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprRegionInputVisitor;

import java.util.Iterator;
import java.util.Set;

/**
 * This class populates the input variables for the region, it does so by computing the first var use for every slot in case of non-method region, or computing the parameters of a method as the input table in case of a method region.
 */

public class InputTable extends StaticTable<Integer> {
    public final IR ir;
    private boolean isMethodRegion;

    public InputTable(IR ir, boolean isMethodRegion, SlotParamTable slotParamTable, Stmt stmt) {
        super("Region Input Table", "var", isMethodRegion ? "param" : "slot");
        this.ir = ir;
        this.isMethodRegion = isMethodRegion;
        if (isMethodRegion) // all parameters are input
            computeMethodInputVars(slotParamTable);
        else {//only first instances of vars to slots execluding defs.
            computeRegionInput(slotParamTable, stmt);
        }
    }

    private InputTable(boolean isMethodRegion, IR ir){
        super("Region Input Table", "var", isMethodRegion ? "param" : "slot");
        this.isMethodRegion = isMethodRegion;
        this.ir = ir;
    }

    /**
     * This populates the InputTable for a methodRegion using the SlotParamTable since the InputTable for methodRegions is contains the same elements of the SlotParamTable.
     * @param slotParamTable Parameter table for a methodRegion.
     */
    private void computeMethodInputVars(SlotParamTable slotParamTable) {
        for (Integer var : slotParamTable.getKeys()) {
            this.add(var, slotParamTable.lookup(var)[0]);
        }
    }

    /**
     * Computes inputs by visiting statement of the region and figuring out the first use of every stack slot that has no def as its first use.
     * @param slotParamTable Table of vars to stack slots.
     * @param stmt Statement of the region.
     */
    private void computeRegionInput(SlotParamTable slotParamTable, Stmt stmt) {
        ExprRegionInputVisitor exprRegionInputVisitor = new ExprRegionInputVisitor(this, slotParamTable);
        RegionInputVisitor regionInputVisitor = new RegionInputVisitor(exprRegionInputVisitor);
        stmt.accept(regionInputVisitor);
    }

    @Override
    public void print() {
        System.out.println("\nprinting " + tableName + " (" + label1 + "->" + label2 + ")");
        table.forEach((v1, v2) -> System.out.println("@w" + v1 + " --------- " + v2));
    }
}

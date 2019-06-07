package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;

import java.util.Iterator;
import java.util.Set;

/**
 * An environment table that holds all vars to types.
 */
public class VarTypeTable extends StaticTable<String> {
    /**
     * Constructor that is used to generate the type table for a method region.
     * @param ir
     */
    public VarTypeTable(IR ir) {
        super("WalaVarTypeTable", " var ", "type");
        StaticTypeIVisitor staticTypeIVisitor = new StaticTypeIVisitor(ir, this, new Pair(-100, -100));

        for (SSAInstruction ins : ir.getControlFlowGraph().getInstructions()) {
            if (ins != null)
                ins.visit(staticTypeIVisitor);
        }

        Iterator<? extends SSAInstruction> phiItr = ir.iteratePhis();
        while (phiItr.hasNext()) {
            SSAInstruction ins = phiItr.next();
            if (ins != null)
                ins.visit(staticTypeIVisitor);
        }
    }

    /**
     * Constructor that is used to generate the type table for a conditional region, by specifying the boundaries of variables inside the region.
     * @param ir Wala IR that corresponds to the method that the region is discovered from.
     * @param firstUseLastDef A pair of the first Use Var and the Last Def Var numbers inside the region.
     */
    public VarTypeTable(IR ir, Pair<Integer, Integer> firstUseLastDef) {
        super("WalaVarTypeTable", " var ", "type");
        StaticTypeIVisitor staticTypeIVisitor = new StaticTypeIVisitor(ir, this, firstUseLastDef);
        for (SSAInstruction ins : ir.getControlFlowGraph().getInstructions()) {
            if (ins != null)
                ins.visit(staticTypeIVisitor);
        }
        Iterator<? extends SSAInstruction> phiItr = ir.iteratePhis();
        while (phiItr.hasNext()) {
            phiItr.next().visit(staticTypeIVisitor);
        }
    }

    /**
     * Default constructor.
     */
    private VarTypeTable() {

        super("WalaVarTypeTable", " var ", "type");
    }


    @Override
    public void print() {
        System.out.println("\nprinting " + tableName + " (" + label1 + "->" + label2 + ")");
        table.forEach((v1, v2) -> System.out.println("@w" + v1 + " --------- " + v2));
    }
}


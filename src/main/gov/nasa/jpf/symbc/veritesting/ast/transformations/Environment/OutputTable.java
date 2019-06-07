package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprBoundaryVisitor;

import java.util.*;

/**
 * An Environment table that holds all slots that needs to be populated after successful symmetrization of the region. Vars associated with the slot are the last instance discovered for the slots.
 */
public class OutputTable extends StaticTable<Integer> {

    public OutputTable(IR ir, boolean isMethodRegion, SlotParamTable slotParamTable, InputTable inputTable, Stmt stmt) {
        super("Region Output Table", isMethodRegion ? "return" : "slot", "var");
        assert (isMethodRegion);
        isMethodRegion = true;
        computeMethodOutput(ir);
    }


    public OutputTable(IR ir,
                       boolean isMethodRegion,
                       SlotParamTable slotParamTable,
                       InputTable inputTable,
                       Stmt stmt,
                       Pair<Integer, Integer> firstDefLastDef) {
        super("Region Output Table", isMethodRegion ? "return" : "slot", "var");
        assert (!isMethodRegion);
        isMethodRegion = false;
        computeOutputVars(ir, slotParamTable, inputTable, firstDefLastDef);
    }

    /**
     * All normal predecessors of an exit node must have a return as the last instruction. If the first return has no use then the method is void.
     * @param ir
     */
    private void computeMethodOutput(IR ir) {
        List<SSAReturnInstruction> returnInsList = findAllReturns(ir);
        int resultNum = 0;
        for (SSAReturnInstruction returnIns : returnInsList) {
            if (returnIns.getNumberOfUses() == 0) {
                return; // a void method, it does not have an output
            } else {
                this.add(resultNum, returnIns.getUse(0));
                ++resultNum;
            }
        }
    }

    private List<SSAReturnInstruction> findAllReturns(IR ir) {
        List<SSAReturnInstruction> returnInsList = new ArrayList<>();
        ISSABasicBlock exitBB = ir.getExitBlock();
        List<ISSABasicBlock> retunBBList = (List<ISSABasicBlock>) ir.getControlFlowGraph().getNormalPredecessors(exitBB);
        for (ISSABasicBlock returnBB : retunBBList) {
            assert (returnBB.getLastInstruction() instanceof SSAReturnInstruction);
            returnInsList.add((SSAReturnInstruction) returnBB.getLastInstruction());
        }
        return returnInsList;
    }

    public OutputTable(boolean isMethodRegion) {
        super("Region Output Table", isMethodRegion ? "return" : "slot", "var");
    }

    /**
     * outputVars are computed by finding the maximum wala var for each stackSlot and those that are not input or constants.
     *
     */
    private void computeOutputVars(IR ir, SlotParamTable slotParamTable, InputTable inputTable, Pair<Integer, Integer> firstDefLastDef) {
        HashSet<Integer> allSlots = slotParamTable.getSlots();
        Iterator<Integer> slotsIter = allSlots.iterator();
        while (slotsIter.hasNext()) {
            int slot = slotsIter.next();
            Set<Integer> varsForSlot = slotParamTable.getVarsOfSlot(slot, firstDefLastDef.getFirst(), firstDefLastDef.getSecond());
            if (!varsForSlot.isEmpty()) {
                Integer slotOutput = Collections.max(varsForSlot);
                if ((inputTable.lookup(slotOutput) == null) && !(ir.getSymbolTable().isConstant(slotOutput)))
                    this.add(slot, Collections.max(varsForSlot));
            }
        }
    }

    @Override
    public void print() {
        System.out.println("\nprinting " + tableName + " (" + label1 + "->" + label2 + ")");
        table.forEach((v1, v2) -> System.out.println(v1 + " --------- @w" + v2));
    }

    public boolean isOutputVar(int var) {
        return table.containsValue(var);
    }
}

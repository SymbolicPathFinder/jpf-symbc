package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprBoundaryVisitor;

import java.util.*;

/**
 * This is the basic table, on which the input and output of the region are defined.
  The table holds the wala vars -> stackSlot mapping if it is not a method region, if it is a method region, then wala vars to parameters to the method are instead populated in this table.
  In case of a non method region, the map holds for every var all the stackSlots that the var
  can map to, because a var can map to multiple locations. Also non-input an non-output vars mapping for non method regions can appear in this table if we were able to infer their stack slot.
 */



public class SlotParamTable extends StaticTable<int[]> {
    private IR ir;
    private boolean isMethodRegion;
    private Stmt stmt;

    public SlotParamTable(IR ir, Boolean isMethodRegion, Stmt stmt) { // var -> param/slot
        super("stack-slot table", "var", isMethodRegion ? "param" : "slot");
        assert(isMethodRegion);
        this.ir = ir;
        this.isMethodRegion = isMethodRegion;
        populateParam();
    }


    public SlotParamTable(IR ir, Boolean isMethodRegion, Stmt stmt, Pair<Integer, Integer> firstUseLastDef,
                          int startingBlockNumber, int terminusBlockNumber) { // var -> param/slot
        super("stack-slot table", "var", isMethodRegion ? "param" : "slot");
        assert(!isMethodRegion);
        this.ir = ir;
        this.isMethodRegion = isMethodRegion;
        this.stmt = stmt;
        populateSlotsForVars(startingBlockNumber, terminusBlockNumber);
    }


    private void populateParam() {
        for (int i = 0; i < ir.getNumberOfParameters(); i++) {
            this.add(ir.getParameter(i), new int[]{i});
        }
    }

    private SlotParamTable(boolean isMethodRegion) {

        super("stack-slot table", "var", isMethodRegion ? "param" : "slot");
    }


    private void populateSlotsForVars(int startingBlockNumber, int terminusBlockNumber) {
        StackSlotIVisitor stackSlotIVisitor = new StackSlotIVisitor(ir, this);
        // visit the region's instructions first to ensure that stack slots corresponding to the region are preferred
        // to stack slots originating from the rest of the method
        for (int bbNum = startingBlockNumber; bbNum <= terminusBlockNumber; bbNum++){
            ISSABasicBlock bb = ir.getControlFlowGraph().getNode(bbNum);
            for (SSAInstruction ins: bb) if (ins != null) ins.visit(stackSlotIVisitor);
            for (Iterator<SSAPhiInstruction> phiItr = bb.iteratePhis(); phiItr.hasNext(); )
                phiItr.next().visit(stackSlotIVisitor);
        }
        for (SSAInstruction ins : ir.getControlFlowGraph().getInstructions()) {
            if (ins != null)
                ins.visit(stackSlotIVisitor);
        }
        for (Iterator<ISSABasicBlock> bbItr = ir.getControlFlowGraph().iterator(); bbItr.hasNext();) {
            for (Iterator<SSAPhiInstruction> phiItr = bbItr.next().iteratePhis(); phiItr.hasNext(); ) {
                phiItr.next().visit(stackSlotIVisitor);
            }
        }
        stackSlotPhiPropagation();
//        filterTableForBoundary(stmt, firstUseLastDef);
    }

    public void filterTable(Pair<Integer, Integer> firstUseLastDef, ArrayList<Integer> allDefs, HashSet<Integer> allUses) {
        Iterator<Integer> keyItr = this.getKeys().iterator();

        while (keyItr.hasNext()) {
            Integer var = keyItr.next();
            // if Wala variable is outside the boundary of the region summary, then remove it
            if ((firstUseLastDef.getFirst() != null && var < firstUseLastDef.getFirst()) ||
                    (firstUseLastDef.getSecond() != null && var > firstUseLastDef.getSecond()))
                keyItr.remove();
            // if Wala variable is not defined in the region summary, then remove it
            else if (!allDefs.contains(var) && !allUses.contains(var)) keyItr.remove();
        }
    }

    /**
     * Finds all unique slots in the stackSlotMap. It attempts to do that by flattening out stackSlots of a single
     var, which can map to multiple locations.
     * @return
     */

    public HashSet getSlots() {
        HashSet<Integer> allSlots = new HashSet();
        Set<Integer> vars = table.keySet();
        Iterator<Integer> varItr = vars.iterator();
        HashSet<Integer> VarSlotSet = new HashSet();

        while (varItr.hasNext()) {
            Integer var = varItr.next();
            int[] varStackSlots = table.get(var);
            for (int i = 0; i < varStackSlots.length; i++) { //silly, converts an array to HashSet, there should be better ways in Java 8.
                VarSlotSet.add(varStackSlots[i]);
            }
            allSlots.addAll(VarSlotSet);
        }
        return allSlots;
    }

    /**
     * Returns all vars that have the same stack slot entered, between boundaries.
     * @param slot A slot number that we wish to discover all vars attaching to it.
     * @param firstVarId A lower bound on the var number to be discovered by this method.
     * @param lastVarId An upper bound on the var numbers to be discovered by this method.
     * @return All vars that have the same stack slot.
     */

    public Set getVarsOfSlot(int slot, Integer firstVarId, Integer lastVarId) {
        HashSet<Integer> stackSlotVars = new HashSet();
        Set<Integer> vars = table.keySet();
        Iterator<Integer> varIter = vars.iterator();

        while (varIter.hasNext()) {
            HashSet<Integer> varSlotSet = new HashSet();
            Integer var = varIter.next();
            int[] varStackSlots = table.get(var);
            for (int i = 0; i < varStackSlots.length; i++) { //silly, converts an array to HashSet, there should be better ways in Java 8.
                varSlotSet.add(varStackSlots[i]);
            }
            if (((lastVarId == null) || ((var <= lastVarId) && (var >= firstVarId))) && (varSlotSet.contains(slot)))
                stackSlotVars.add(var);
        }
        return stackSlotVars;
    }

    /**
     * This tries to infer the stack slots for phi "def" vars and phi "use" vars by either figuring out the stack slots
      of one "use" var and populate it to be for the phi "def" var, or the opposite,
      that is the stack slot of the phi "def" was known and so it is propagated to the "use" vars
     */

    private void stackSlotPhiPropagation() {
        boolean changeDetected;
        do {
            changeDetected = false;
            Iterator<? extends SSAInstruction> phiItr = ir.iteratePhis();
            while (phiItr.hasNext()) {
                SSAPhiInstruction phi = (SSAPhiInstruction) phiItr.next();
                int result = phi.getDef();
                int[] phiSlot = lookup(result);
                if (phiSlot == null) { //stack slot of the phi "def" var is unkown
                    int[] slots = getOperandSlot(phi);
                    if (slots != null) {//could figure out the stack slot of a "use"
                        table.put(phi.getDef(), slots);
                        changeDetected = true;
                    }
                } else { //stack slot of the phi "def" var is unkown, propagate it to the "use" vars
                    changeDetected = updatePhiUse(phi, phiSlot);
                }
            }
        } while (changeDetected);
    }

    private boolean updatePhiUse(SSAPhiInstruction phi, int[] slots) {
        boolean changeDetected = false;
        for (int i = 0; i < phi.getNumberOfUses(); i++) {
            if (!isConstant(phi.getUse(i))) {
                int[] useSckSlot = lookup(phi.getUse(i));
                if (useSckSlot == null) {
                    table.put(phi.getUse(i), slots);
                    changeDetected = true;
                }
            }
        }
        return changeDetected;
    }

    private int[] getOperandSlot(SSAPhiInstruction phi) {
        for (int i = 0; i < phi.getNumberOfUses(); i++) {
            int[] useSckSlot = lookup(phi.getUse(i));
            if (useSckSlot != null)
                return useSckSlot;
        }
        return null;
    }

    /**
     * Determines if a wala var is constant.
     *
     */
    public boolean isConstant(int operand1) {
        SymbolTable table = ir.getSymbolTable();
        return table.isNumberConstant(operand1) ||
                table.isBooleanOrZeroOneConstant(operand1) ||
                table.isNullConstant(operand1);
    }

    @Override
    public void print() {
        System.out.println("\nRegion Stack Slot Map (var -> " + (isMethodRegion ? "param" : "slot") + ")");
        table.forEach((var, stackSlots) -> System.out.println("@w" + var + " --------- " + Arrays.toString(stackSlots)));
    }

}

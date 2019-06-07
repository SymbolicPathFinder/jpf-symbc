package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.FirstITEStmtVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.vm.StackFrame;
import ia_parser.Exp;
import za.ac.sun.cs.green.expr.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

/**
 * Visits expression in a conditional statement to check if any of its arguments are indeed symbolic.
 */
public class SymbCondVisitor implements ExprVisitor<Expression> {
    private final boolean findStackSlotsOnly;
    private final SymbolTable symbolTable;
    public boolean stackSlotNotFound;
    public HashSet<WalaVarExpr> noStackSlotVars;
    private boolean isSymCondition = false;
    private boolean foundWalaVarExpr = false;
    private SlotParamTable slotParamTable;
    private StackFrame sf;
    public final ExprVisitorAdapter<Expression> eva =
            new ExprVisitorAdapter<Expression>(this);


    public SymbCondVisitor(StackFrame sf, SlotParamTable slotParamTable, boolean findStackSlotsOnly, SymbolTable symbolTable) {
        this.slotParamTable = slotParamTable;
        this.sf = sf;
        this.findStackSlotsOnly = findStackSlotsOnly;
        this.stackSlotNotFound = false;
        noStackSlotVars = new HashSet<>();
        this.symbolTable = symbolTable;
    }

    public Expression visit(WalaVarExpr expr) {
        foundWalaVarExpr = true;
        if (!isSymCondition) {
            int[] slots = slotParamTable.lookup(expr.number);
            int slot;
            if (slots != null && !findStackSlotsOnly){
                slot = slots[0];
                gov.nasa.jpf.symbc.numeric.Expression operand = (gov.nasa.jpf.symbc.numeric.Expression)
                        sf.getSlotAttr(slot);
                if (operand != null)
                    isSymCondition = true;
            }
            if(slots == null && !symbolTable.isConstant(expr.number)) {
                stackSlotNotFound = true;
                noStackSlotVars.add(expr);
            }
        }
        return null;
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return null;
    }

    @Override
    public Expression visit(ArrayRefVarExpr expr) {
        return null;
    }

    @Override
    public Expression visit(GammaVarExpr expr) {
        return null;
    }

    @Override
    public Expression visit(IntConstant expr) {
        return null;
    }

    @Override
    public Expression visit(IntVariable expr) {
        return null;
    }

    @Override
    public Expression visit(AstVarExpr expr) { return null; }

    @Override
    public Expression visit(Operation expr) {
        Expression [] operands = new Expression [expr.getArity()];
        int index = 0;
        for (Expression e: expr.getOperands()) {
            operands[index++] = eva.accept(e);
        }
        return null;
    }

    @Override
    public Expression visit(RealConstant expr) {
        return null;
    }

    @Override
    public Expression visit(RealVariable expr) {
        return null;
    }

    @Override
    public Expression visit(StringConstantGreen expr) {
        return null;
    }

    @Override
    public Expression visit(StringVariable expr) {
        return null;
    }

    @Override
    public Expression visit(IfThenElseExpr expr) {
        eva.accept(expr.condition);
        return null;
    }

    public boolean isSymCondition() {
        return isSymCondition;
    }

    public boolean isFoundWalaVarExpr() {
        return foundWalaVarExpr;
    }

    public static HashSet<WalaVarExpr> execute(IR ir, SlotParamTable slotParamTable, Stmt staticStmt) {
        SymbCondVisitor symbCondVisitor = new SymbCondVisitor(null, slotParamTable, true, ir.getSymbolTable());
        ExprVisitorAdapter eva = symbCondVisitor.eva;
        Triple<Expression, ArrayList<GetInstruction>, ArrayList<ArrayLoadInstruction>> triple = FirstITEStmtVisitor.execute(staticStmt);
        eva.accept(triple.getFirst());
        for (GetInstruction getInstruction: triple.getSecond()) {
            if (getInstruction.def instanceof WalaVarExpr &&
                    symbCondVisitor.noStackSlotVars.contains(getInstruction.def))
                symbCondVisitor.noStackSlotVars.remove(getInstruction.def);
        }
        for (ArrayLoadInstruction arrayLoad: triple.getThird()) {
            if (arrayLoad.def instanceof WalaVarExpr &&
                    symbCondVisitor.noStackSlotVars.contains(arrayLoad.def))
                symbCondVisitor.noStackSlotVars.remove(arrayLoad.def);
        }
        return symbCondVisitor.noStackSlotVars;
    }
}

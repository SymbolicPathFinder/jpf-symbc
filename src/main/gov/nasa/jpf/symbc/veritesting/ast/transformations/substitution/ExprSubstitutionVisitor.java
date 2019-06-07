package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.*;

/**
 * This is the expression visitor class used during substitution that either returns the value of a variable from a symbol table to returns the expression back if it doesn't make to any entry.
 */
public class ExprSubstitutionVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    private ThreadInfo ti;
    private StackFrame sf;
    public ExprVisitorAdapter eva;
    private DynamicRegion dynRegion;
    private DynamicTable valueSymbolTable;

    private boolean somethingChanged;

    public boolean isSomethingChanged() {
        return somethingChanged;
    }

    public void setValueSymbolTable(DynamicTable valueSymbolTable){this.valueSymbolTable = valueSymbolTable;}

    public DynamicTable getValueSymbolTable(){return valueSymbolTable;}

    public ExprSubstitutionVisitor(ThreadInfo ti, DynamicRegion dynRegion,
                                   DynamicTable valueSymbolTable) {
        super();
        this.ti = ti;
        this.sf = ti.getTopFrame();
        eva = super.eva;
        this.dynRegion = dynRegion;
        this.valueSymbolTable = valueSymbolTable;
    }


    @Override
    public Expression visit(WalaVarExpr expr) {
        Expression varValue = (Expression) valueSymbolTable.lookup(expr);
        if (varValue instanceof IntConstant) {
            if (dynRegion.inputTable.lookup(expr) != null &&
                    sf.isReferenceSlot(((Integer)dynRegion.inputTable.lookup(expr))) && !dynRegion.isMethodRegion) {
                int objRef = ((IntConstant) varValue).getValue();
                if (objRef == 0) dynRegion.varTypeTable.table.put(expr, "int");
                else dynRegion.varTypeTable.table.put(expr, ti.getElementInfo(objRef).getType());
            }
        }
        if (dynRegion.outputTable.reverseLookup(expr) != null &&
                sf.isReferenceSlot(dynRegion.outputTable.reverseLookup(expr)) && !dynRegion.isMethodRegion) {
            int slot = dynRegion.outputTable.reverseLookup(expr);
            gov.nasa.jpf.symbc.numeric.Expression useForTypeOnly =
                    (gov.nasa.jpf.symbc.numeric.Expression) sf.getLocalAttr(slot);
            int objRef;
            if (useForTypeOnly == null)
                objRef = sf.getLocalVariable(slot);
            else objRef = (useForTypeOnly instanceof IntegerConstant) ? (int) ((IntegerConstant) useForTypeOnly).value : -1;
            if (objRef != -1 && objRef != 0) dynRegion.varTypeTable.table.put(expr, ti.getElementInfo(objRef).getType());
            else dynRegion.varTypeTable.table.put(expr, "int");
        }
        if (varValue != null) {
            somethingChanged = true;
            return varValue;
        } else
            return expr;
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return expr;
    }

    public static StaticRegionException sre = new StaticRegionException("region substitution problem in ExprSubstitutionVisitor.");


}

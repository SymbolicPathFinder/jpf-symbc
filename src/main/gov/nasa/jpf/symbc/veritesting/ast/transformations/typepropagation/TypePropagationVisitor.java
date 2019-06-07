package gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Set;

public class TypePropagationVisitor extends AstMapVisitor {
    private DynamicTable varTypeTable;
    private ExprVisitorAdapter<Expression> eva;

    public TypePropagationVisitor(DynamicTable varTypeTable) {
        super(new ExprTypeVisitor(varTypeTable));
        this.varTypeTable = varTypeTable;
        eva = super.eva;
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        ((ExprTypeVisitor)exprVisitor).latestType = null;
        eva.accept(a.rhs);
        if (a.lhs instanceof WalaVarExpr) {
            varTypeTable.add(((WalaVarExpr) a.lhs).number, ((ExprTypeVisitor)exprVisitor).latestType);
        }
        return a;
    }

    public static DynamicTable propagateTypes(DynamicRegion dynRegion) {
        TypePropagationVisitor visitor = new TypePropagationVisitor(dynRegion.varTypeTable);
        dynRegion.dynStmt.accept(visitor);
        return visitor.varTypeTable;
    }

}

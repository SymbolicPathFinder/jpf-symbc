package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import jkind.lustre.NamedType;
import jkind.lustre.VarDecl;
import za.ac.sun.cs.green.expr.*;

import java.util.ArrayList;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.stringToLusterType;

public class DeclarationExprVisitor implements ExprVisitor {
    private final DynamicRegion dynRegion;
    private final InOutManager inOutManager;
    public ArrayList<VarDecl> declarationList = new ArrayList<>();

    public DeclarationExprVisitor(DynamicRegion dynRegion, InOutManager inOutManager) {
        this.dynRegion = dynRegion;
        this.inOutManager = inOutManager;
    }

    @Override
    public Object visit(IntConstant expr) {
        return null;
    }

    @Override
    public Object visit(IntVariable expr) {
        if (!inOutManager.isInOutVar(expr.toString(), NamedType.INT)) { // if it is not input or output in it is a
            // local var
            // that
            // we care about adding
            VarDecl lusterVar = new VarDecl(expr.toString(), NamedType.INT);
            declarationList.add(lusterVar);
        }
        return null;
    }

    @Override
    public Object visit(Operation expr) {
        return null;
    }

    @Override
    public Object visit(RealConstant expr) {
        return null;
    }

    @Override
    public Object visit(RealVariable expr) {
        if (!inOutManager.isInOutVar(expr.toString(), NamedType.REAL)) { // if it is not input or output in it is a
            // local var
            // that we care about adding
            VarDecl lusterVar = new VarDecl(expr.toString(), NamedType.REAL);
            declarationList.add(lusterVar);
        }
        return null;
    }

    @Override
    public Object visit(StringConstantGreen expr) {
        return null;
    }

    @Override
    public Object visit(StringVariable expr) {
    /*    if (inOutManager.isInOutVar(expr.toString(), lusterStringType)) { // if it is not input or output in it is a local var
            // that we care about adding
            VarDecl lusterVar = new VarDecl(expr.toString(), lusterStringType);
            declarationList.add(lusterVar);
        }*/
        System.out.println("un-supported var type");
        assert false;
        return null;
    }

    @Override
    public Object visit(IfThenElseExpr expr) {
        return null;
    }

    @Override
    public Object visit(ArrayRefVarExpr expr) {
        return null;
    }

    @Override
    public Object visit(WalaVarExpr expr) {
        Object rangerType = dynRegion.varTypeTable.lookupByName(expr.toString());
        if(rangerType.equals("boolean")) //converting boolean to spf presentation as int
            rangerType = "int";
        assert (rangerType instanceof String);
        NamedType lusterType = stringToLusterType((String) rangerType);
        if (!inOutManager.isInOutVar(expr.toString(), lusterType)) { // if it is not input or output in it is a local
            // var that
            // we care about adding
            VarDecl lusterVar = new VarDecl(expr.toString(), lusterType);
            declarationList.add(lusterVar);
        }
        return null;
    }

    @Override
    public Object visit(FieldRefVarExpr expr) {
        String rangerType = dynRegion.fieldRefTypeTable.lookupByName(expr.toString());
        if(rangerType.equals("boolean")) //converting boolean to spf presentation as int
            rangerType = "int";
        NamedType lusterType = stringToLusterType(rangerType);
        if (!inOutManager.isInOutVar(expr.toString(), lusterType)) { // if it is not input or output in it is a local
            // var that
            // we care about adding
            VarDecl lusterVar = new VarDecl(expr.toString(), lusterType);
            declarationList.add(lusterVar);
        }
        return null;
    }

    @Override
    public Object visit(GammaVarExpr expr) {
        return null;
    }

    //TODO
    @Override
    public Object visit(AstVarExpr expr) {
        System.out.println("unsupported translation");
        assert false;
        return null;
    }
}

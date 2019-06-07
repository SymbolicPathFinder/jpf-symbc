package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import jkind.lustre.VarDecl;

import java.util.ArrayList;

public class DeclarationTranslator {


    public static ArrayList<VarDecl> execute(DynamicRegion dynamicRegion, InOutManager inOutManager){
        DeclarationExprVisitor declarationExprVisitor = new DeclarationExprVisitor(dynamicRegion, inOutManager);
        AstMapVisitor astMapVisitor = new DeclarationStmtVisitor(declarationExprVisitor);
        dynamicRegion.dynStmt.accept(astMapVisitor);
        return declarationExprVisitor.declarationList;
    }
}

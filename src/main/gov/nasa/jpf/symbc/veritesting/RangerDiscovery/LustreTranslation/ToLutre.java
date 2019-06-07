package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.lustre.*;
import jkind.lustre.parsing.LustreParseUtil;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.varDeclToIdExpr;

public class ToLutre {


    public static Node generateRnode(DynamicRegion dynamicRegion, Contract contract) {
        InOutManager inOutManager = contract.inOutManager;
        ArrayList<VarDecl> localDeclList = DeclarationTranslator.execute(dynamicRegion, inOutManager);
        localDeclList.add(addSymVar());
        ArrayList<Equation> equationList = EquationVisitor.execute(dynamicRegion);
        equationList.addAll(inOutManager.getTypeConversionEq()); // adding type conversion equations.
        localDeclList.addAll(inOutManager.getConversionLocalList());
        equationList.add(addSymVarEquation());
        ArrayList<VarDecl> inputDeclList = inOutManager.generateInputDecl();
        ArrayList<VarDecl> ouputDeclList = inOutManager.generateOutputDecl();
        ArrayList<VarDecl> methodOutDeclList = inOutManager.generaterMethodOutDeclList();
        ouputDeclList.addAll(methodOutDeclList);
        return new Node("R_node", inputDeclList, ouputDeclList, localDeclList, equationList, new ArrayList<>(),
                new ArrayList<>(), null, null, null);
    }

    //adding symVar equation, this can be taken out if we do not need symVar wrapper
    private static Equation addSymVarEquation() {
        return new Equation(new IdExpr("symVar"), new IntExpr(1));
    }

    //adding symVar declaration, this can be taken out if we do not need symVar wrapper
    private static VarDecl addSymVar() {
        return new VarDecl("symVar", NamedType.INT);
    }

    public static Node generateRwrapper(InOutManager inOutManager) {
        List<VarDecl> freeDeclList = inOutManager.generateFreeInputDecl();

        //wrapperLocals are defined as stateInput
        ArrayList<VarDecl> stateInDeclList = inOutManager.generateStateInputDecl();
        ArrayList<VarDecl> wrapperLocalDeclList = new ArrayList<>(stateInDeclList);

        //preparing wrapperOutput
        Pair<VarDecl, Equation> methodOutVarEq = DiscoveryUtil.replicateToOut(stateInDeclList.get(stateInDeclList.size()-1),"out");
        ArrayList<VarDecl> wrapperOutput = new ArrayList<VarDecl>();
        wrapperOutput.add(methodOutVarEq.getFirst());

        //call node_R
        ArrayList<Expr> actualParameters = new ArrayList<>();
        actualParameters.addAll(varDeclToIdExpr(freeDeclList));
        actualParameters.addAll(initPreTerm(wrapperLocalDeclList));
        NodeCallExpr r_nodeCall = new NodeCallExpr("R_node", actualParameters);
        Equation wrapperEq = new Equation(varDeclToIdExpr(wrapperLocalDeclList), r_nodeCall);

        ArrayList<Equation> wrapperEqList = new ArrayList<Equation>();
        wrapperEqList.add(wrapperEq);
        wrapperEqList.add(methodOutVarEq.getSecond()); //adding equation for output

        return new Node("R_wrapper", freeDeclList, wrapperOutput, wrapperLocalDeclList, wrapperEqList
                , new ArrayList<>(), new ArrayList<>(), null, null, null);
    }

    private static ArrayList<Expr> initPreTerm(ArrayList<VarDecl> wrapperLocalDeclList) {
        ArrayList<Expr> initPreExprList = new ArrayList<>();

        for (int i = 0; i < wrapperLocalDeclList.size(); i++) {
            initPreExprList.add(new BinaryExpr(new BoolExpr(false), BinaryOp.ARROW, new UnaryExpr(UnaryOp.PRE,
                    varDeclToIdExpr(wrapperLocalDeclList.get(i)))));
        }
        return initPreExprList;
    }


    public static Program generateTprogram(String tFileName){
        String programStr = null;
        try {
            programStr = new String(Files.readAllBytes(Paths.get(tFileName)), "UTF-8");

        } catch (IOException e) {
            System.out.println("Problem reading file. " + e.getMessage());
        }

        Program program = LustreParseUtil.program(programStr);
        return program;
    }
    /**
     * used to remove "." and "$" from the text generated to make it type compatible.
     *
     * @param node
     * @return
     */
    public static String lustreFriendlyString(Object node) {
        String nodeStr = node.toString();
        nodeStr = nodeStr.replaceAll("\\.", "_");
        nodeStr = nodeStr.replaceAll("\\$", "_");
        return nodeStr;
    }

/*

    */
/**
 * This method attaches a dummy true property to "node"
 * @param node
 * @return
 *//*

    public static Node addDummyTrueProp(Node node){
        node.locals.add(new VarDecl("dummyProp", NamedType.BOOL));
        node.equations.add(new Equation(new IdExpr("dummyProp"), new BoolExpr(true)));
        node.properties.add("dummyProp");
        return node;
    }
*/
}

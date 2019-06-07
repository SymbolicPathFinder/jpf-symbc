package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;

public class InputOutput {
    public ArrayList<Pair<String, NamedType>> varList = new ArrayList<>();

    public void add(String start_btn, NamedType type) {
        varList.add(new Pair<>(start_btn, type));
    }

    public boolean contains(String varName, NamedType type) {
        for (int i = 0; i < varList.size(); i++) {
            if (varList.get(i).getFirst().equals(varName) && varList.get(i).getSecond().equals(type))
                return true;
        }
        return false;
    }

    public ArrayList<VarDecl> generateVarDecl() {
        ArrayList<VarDecl> varDeclList = new ArrayList<>();

        for (int i = 0; i < varList.size(); i++) {
            Pair<String, NamedType> var = varList.get(i);
            varDeclList.add(new VarDecl(var.getFirst(), var.getSecond()));
        }
        return varDeclList;
    }


    public Pair<ArrayList<VarDecl>, ArrayList<Equation>> convertInput() { //convertBoolToSpfInt
        ArrayList<Equation> conversionEqList = new ArrayList<>();
        ArrayList<VarDecl> conversionLocalList = new ArrayList<>();

        for (int i = 0; i < varList.size(); i++) {
            String var = varList.get(i).getFirst();
            NamedType type = varList.get(i).getSecond();
            if (type == NamedType.BOOL) { //type conversion needed
                conversionLocalList.add(new VarDecl(var, NamedType.INT));
                String newVar = var + "_bool";
                varList.set(i, new Pair(newVar, NamedType.BOOL));
                IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(new IdExpr(newVar), new IntExpr(1), new IntExpr(0));
                Equation conversionEq = new Equation(new IdExpr(var), ifThenElseExpr);
                conversionEqList.add(conversionEq);
            }

        }
        return new Pair(conversionLocalList, conversionEqList);
    }

    public Pair<ArrayList<VarDecl>, ArrayList<Equation>> convertOutput() { // convertSpfIntToBool
        ArrayList<Equation> conversionEqList = new ArrayList<>();
        ArrayList<VarDecl> conversionLocalList = new ArrayList<>();

        for (int i = 0; i < varList.size(); i++) {
            String var = varList.get(i).getFirst();
            NamedType type = varList.get(i).getSecond();
            if (type == NamedType.BOOL) { //type conversion needed
                conversionLocalList.add(new VarDecl(var, NamedType.INT));
                String newVar = var + "_bool";
                varList.set(i, new Pair(newVar, NamedType.BOOL));
                IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(new BinaryExpr(new IdExpr(var), BinaryOp.EQUAL, new
                        IntExpr
                        (1)), new BoolExpr(true), new BoolExpr(false));
                Equation conversionEq = new Equation(new IdExpr(newVar), ifThenElseExpr);
                conversionEqList.add(conversionEq);
            }

        }
        return new Pair(conversionLocalList, conversionEqList);
    }

    //this is very specific to r_wrapper and is used particularly to replicate the methodOutput, that is part of the state, to become the output of the wrapper.
    public Pair<VarDecl, Equation> replicateMe(String myNewName) {
        assert (varList.size() == 1);

        Pair<String, NamedType> methodOutVar = varList.get(0);

        VarDecl out = new VarDecl(myNewName, methodOutVar.getSecond());

        Equation outEq = new Equation(DiscoveryUtil.varDeclToIdExpr(out), new IdExpr(methodOutVar.getFirst()));

        return new Pair(out, outEq);
    }
}

package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.lang.reflect.Array;
import java.util.ArrayList;


/**
 * this class manages the input and output of RNode, it assumes that the input and the output of the "step" function is
 * provided, it is divided into 4 types, freeInput, stateInput, stateOutput and methodOutput. The type of those
 * should match the signature of the step function. Type conversion is needed sometimes, if so then the variable
 * names in the arraylist will change to the new var being created, in this case there will be as well a side effect
 * for the equations needed for conversion between the original var and the new var being created for conversion.
 */
public class InOutManager {

    InputOutput freeInput = new InputOutput();
    InputOutput stateInput = new InputOutput();
    InputOutput stateOutput = new InputOutput();
    InputOutput methodOutput = new InputOutput();

    ArrayList<Equation> typeConversionEq = new ArrayList<>();
    ArrayList<VarDecl> conversionLocalList = new ArrayList<>();

    public ArrayList<Equation> getTypeConversionEq() {
        return typeConversionEq;
    }

    public ArrayList<VarDecl> getConversionLocalList() {
        return conversionLocalList;
    }

    public void discoverVars() {
        discoverFreeInput();
        discoverStateInput();
        discoverStateOutput();
        discoverMethodOutput();
    }

    //entered by hand for now
    private void discoverMethodOutput() {
        methodOutput.add("r347.ignition_r.1.7.4", NamedType.BOOL);
        Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = methodOutput.convertOutput();
        typeConversionEq.addAll(conversionResult.getSecond());
        //conversionLocalList.addAll(conversionResult.getFirst()); // no need to add this, since these are already as
        // def in the dynStmt
    }

    //entered by hand for now
    private void discoverFreeInput() {
        freeInput.add("signal", NamedType.INT);
    }

    //entered by hand for now
    private void discoverStateInput() {
        stateInput.add("start_btn", NamedType.BOOL);
        stateInput.add("launch_btn", NamedType.BOOL);
        stateInput.add("reset_btn", NamedType.BOOL);
        stateInput.add("ignition", NamedType.BOOL);

        Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = stateInput.convertInput();
        typeConversionEq.addAll(conversionResult.getSecond());
        conversionLocalList.addAll(conversionResult.getFirst());
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutput() {
        stateOutput.add("r347.start_btn.1.15.4", NamedType.BOOL);
        stateOutput.add("r347.launch_btn.1.17.4", NamedType.BOOL);
        stateOutput.add("r347.reset_btn.1.9.4", NamedType.BOOL);

        Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = stateOutput.convertOutput();
        typeConversionEq.addAll(conversionResult.getSecond());
        //conversionLocalList.addAll(conversionResult.getFirst()); // no need to add this, since these are already as
        // def in the dynStmt
    }

    public ArrayList<VarDecl> generateInputDecl() {
        ArrayList<VarDecl> inputDeclList = generateFreeInputDecl();
        inputDeclList.addAll(generateStateInputDecl());
        return inputDeclList;
    }
    public ArrayList<VarDecl> generateFreeInputDecl(){
        return generateLustreDecl(freeInput);
    }

    public ArrayList<VarDecl> generateStateInputDecl(){
        return generateLustreDecl(stateInput);
    }

    private ArrayList<VarDecl> generateLustreDecl(InputOutput inputOutput) {
        return inputOutput.generateVarDecl();
    }

    public ArrayList<VarDecl> generaterMethodOutDeclList() {
        return methodOutput.generateVarDecl();
    }

    public ArrayList<VarDecl> generateOutputDecl() {
        return stateOutput.generateVarDecl();
    }

    /**
     * searches in all in input and output arrays to check if it is one in them
     *
     * @param s
     * @return
     */
    public boolean isInOutVar(String s, NamedType type) {
        return isFreeInVar(s, type) || isStateInVar(s, type) || isStateOutVar(s, type) || isMethodOutVar(s, type);
    }


    public boolean isFreeInVar(String varName, NamedType type) {
        return freeInput.contains(varName, type);
    }

    public boolean isStateInVar(String varName, NamedType type) {
        return stateInput.contains(varName, type);
    }

    public boolean isStateOutVar(String varName, NamedType type) {
        return stateOutput.contains(varName, type);
    }

    public boolean isMethodOutVar(String varName, NamedType type) {
        return methodOutput.contains(varName, type);
    }

    public Pair<VarDecl, Equation> replicateMethodOutput(String outVarName){
        return methodOutput.replicateMe(outVarName);
    }

}

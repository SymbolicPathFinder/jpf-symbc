package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.Main;
import jkind.lustre.Node;
import jkind.lustre.Program;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.writeToFile;

public class DiscoverContract {
    /**
     * name of the method we want to extract its contract.
     */
    public static boolean contractDiscoveryOn = false;
    public static boolean called = false;

    public static LinkedHashSet<Pair> z3QuerySet = new LinkedHashSet();

    //TODO: These needs to be configured using the .jpf file.
    public static String folderName = "../src/DiscoveryExamples/";
    static String tFileName = folderName + "ImaginaryPad";

/***** begin of unused vars***/
    /**
     * currently unused because we assume we have a way to find the input and output.
     * This later needs to be changed to generalize it by looking only at the method
     * and the class of interest.
     */
    public static String contractMethodName;
    public static String className;
    public static String packageName;

    /***** end of unused vars***/

    public static final ArrayList<Node> discoverLusterContract(DynamicRegion dynamicRegion) {

        if (!called) { //print out the translation once, for very first time we hit linearlization for the method of
            // interest.
            Contract contract = new Contract();
            Node rNode = ToLutre.generateRnode(dynamicRegion, contract);
            Node rWrapper = ToLutre.generateRwrapper(contract.inOutManager);
            TProgram tProgram = new TProgram(tFileName);
            //it is always the case the the last node in a tProgram is tNode
            assert (tProgram.nodes.get(tProgram.nodes.size() - 1).id.equals("T_node"));
            Node mainNode = tProgram.generateMainNode(tProgram.nodes.get(tProgram.nodes.size() - 1), rWrapper, contract
                    .inOutManager);

            ArrayList<Node> cdNodeList = new ArrayList<>();
            cdNodeList.addAll(tProgram.nodes);
            cdNodeList.add(rNode);
            cdNodeList.add(rWrapper);
            cdNodeList.add(mainNode);
            String rNodeLustreFriendlyStr = ToLutre.lustreFriendlyString(rNode);
            String rWrapperLustreFriendlyStr = ToLutre.lustreFriendlyString(rWrapper);
            String mainNodeLustreFriendlyStr = ToLutre.lustreFriendlyString(mainNode);

            String mergedContracts = rNodeLustreFriendlyStr + rWrapperLustreFriendlyStr + tProgram
                    .toString() + mainNodeLustreFriendlyStr;
            writeToFile(contractMethodName + ".lus", mergedContracts);

            callJkind();

        }
        called = true;
        return null;
    }

    private static void callJkind() {
        String[] jkindArgs = new String[5];
        jkindArgs[0] = "-jkind";
        jkindArgs[1] = folderName + contractMethodName + ".lus";
        jkindArgs[2] = "-solver";
        jkindArgs[3] = "z3";
        jkindArgs[4] = "-scratch";
        Main.main(jkindArgs);
    }


    //ToDo: not sure if this works, I need to test the change.
    public static String toSMT(String solver, HashSet z3FunDecl) {
        return Z3Format.toSMT(solver, z3FunDecl);
    }
}

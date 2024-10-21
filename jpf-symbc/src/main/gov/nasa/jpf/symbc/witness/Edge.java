/**
 * Object that represents a single edge of the violation witness
 * It has two methods, serializeEdge() and serializeAllEdges()
 * Variable indexOfEdge denotes an index of the node
 * Variable fileName denotes the value of the key "originfile" in the edge
 * Variable assumptionScope denotes the value of the key "assumption.scope" in the edge
 * Variable allowMethodInvocation is a flag that shows whether invocation of method is allowed
 * to represent the string value of assumption or not
 * List symbolicVariableInfoList is a list that contains the value of
 * the key "startline" and "assumption"
 */

package gov.nasa.jpf.symbc.witness;

import java.util.List;


public class Edge{
    /**
     * Denotes an index of node. For example, if source node is n0 and target node is n1, index of node will be 0.
     */
    public int indexOfEdge;
    /**
     * Denotes a name of file and a value of "originfile" in violation witness.
     * For example, if you are running Main.java, filename will be "Main.java".
     */
    public String fileName;
    /**
     * A list that contains information of symbolic variables such as value of symbolic variable or line number.
     */
    public List<SymbolicVariableInfo> symbolicVariableInfoList;
    /**
     * Denotes a value of "assumption.scope" in violation witness.
     */
    public String assumptionScope;
    /**
     * A flag to check allow method invocation in assumption.
     * For example, if we want to express string value with equals() method, this flag should be true
     */
    public boolean allowMethodInvocation;

    public Edge(int indexOfEdge, String fileName, List<SymbolicVariableInfo> symbolicVariableInfoList, boolean allowMethodInvocation, String assumptionScope){
        this.indexOfEdge = indexOfEdge;
        this.fileName = fileName;
        this.symbolicVariableInfoList = symbolicVariableInfoList;
        this.allowMethodInvocation = allowMethodInvocation;
        this.assumptionScope = assumptionScope;
    }

    /**
     * It serializes a single edge of the violation witness
     * @return A string that represents single edge
     */
    private String serializeEdge(){

        StringBuilder edgeBuilder = new StringBuilder();
        edgeBuilder.append(String.format("       <edge source=\"n%d\" target=\"n%d\">\n", indexOfEdge, indexOfEdge+1));
        //edgeId += System.lineSeparator();
        edgeBuilder.append(String.format("         <data key=\"originfile\">%s.java</data>\n", fileName));
        //edgeId += System.lineSeparator();
        edgeBuilder.append(String.format("         <data key=\"startline\">%d</data>\n", symbolicVariableInfoList.get(indexOfEdge).lineNumber));
        // If variable value is null, it means that this variable doesn't appear in PC
        // (i.e. it doesn't matters program's correctness. In this case, just put arbitrary default value)
        if(symbolicVariableInfoList.get(indexOfEdge).returnType.equals("double") ||
                symbolicVariableInfoList.get(indexOfEdge).returnType.equals("float")){
            if(symbolicVariableInfoList.get(indexOfEdge).varValue == null) {
                edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %f</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, 2.0));
            }
            else edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %f</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, symbolicVariableInfoList.get(indexOfEdge).varValue));
        }

        else if(symbolicVariableInfoList.get(indexOfEdge).returnType.equals("boolean")){
            if(symbolicVariableInfoList.get(indexOfEdge).varValue == null) edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %b</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, true));
            else edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %b</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, symbolicVariableInfoList.get(indexOfEdge).varValue));
        }

        else if(symbolicVariableInfoList.get(indexOfEdge).returnType.equals("java.lang.String")){
            if(allowMethodInvocation){
                if(symbolicVariableInfoList.get(indexOfEdge).varValue == null) edgeBuilder.append(String.format("         <data key=\"assumption\">%s.equals(%s)</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, "\"\""));
                else edgeBuilder.append(String.format("         <data key=\"assumption\">%s.equals(%s)</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, symbolicVariableInfoList.get(indexOfEdge).varValue));
            }
            else{
                if(symbolicVariableInfoList.get(indexOfEdge).varValue == null) edgeBuilder.append(String.format("         <data key=\"assumption\">%s==%s</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, "\"\""));
                else edgeBuilder.append(String.format("         <data key=\"assumption\">%s==%s</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, symbolicVariableInfoList.get(indexOfEdge).varValue));
            }
        }

        else{
            // Here, the type of symbolic variable should be integer or char.
            assert(symbolicVariableInfoList.get(indexOfEdge).returnType.equals("int") ||
                    symbolicVariableInfoList.get(indexOfEdge).returnType.equals("char"));
            if(symbolicVariableInfoList.get(indexOfEdge).varValue == null) edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %d</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, 4));
            else edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %d</data>\n", symbolicVariableInfoList.get(indexOfEdge).varPgmName, symbolicVariableInfoList.get(indexOfEdge).varValue));
        }

        edgeBuilder.append(String.format("         <data key=\"assumption.scope\">java::L%s;</data>\n", assumptionScope));

        edgeBuilder.append("       </edge>\n");
        return edgeBuilder.toString();
    }

    /**
     * It serializes every edge in edgeList
     * @param edgeList contains all edges of the violation witness
     * @return A string that represents every edge of the violation witness
     */
    public static String serializeAllEdges(List<Edge> edgeList){
        StringBuilder allEdgesBuilder = new StringBuilder();
        for(Edge edge : edgeList){
            allEdgesBuilder.append(edge.serializeEdge());
        }
        return allEdgesBuilder.toString();
    }

}

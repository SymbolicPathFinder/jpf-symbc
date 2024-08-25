package gov.nasa.jpf.symbc.witness;

import java.util.List;


public class Edge{
    public int indexOfEdge;
    public String fileName;

    public List<SymbolicVariableInfo> symbolicVariableInfoList;

    public String assumptionScope;

    public boolean allowMethodInvocation;

    public Edge(int indexOfEdge, String fileName, List<SymbolicVariableInfo> symbolicVariableInfoList, boolean allowMethodInvocation, String assumptionScope){
        this.indexOfEdge = indexOfEdge;
        this.fileName = fileName;
        this.symbolicVariableInfoList = symbolicVariableInfoList;
        this.allowMethodInvocation = allowMethodInvocation;
        this.assumptionScope = assumptionScope;
    }
    private String serializeEdge(){
        // later, I have to handle the case when length == 0 and string type for assumption
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
                edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %f</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName, 2.0));
            }
            else edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %f</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName, symbolicVariableInfoList.get(indexOfEdge).varValue));
        }

        else if(symbolicVariableInfoList.get(indexOfEdge).returnType.equals("boolean")){
            if(symbolicVariableInfoList.get(indexOfEdge).varValue == null) edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %b</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName, false));
            else edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %b</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName, symbolicVariableInfoList.get(indexOfEdge).varValue));
        }

        else if(symbolicVariableInfoList.get(indexOfEdge).returnType.equals("java.lang.String")){
            if(allowMethodInvocation){
                if(symbolicVariableInfoList.get(indexOfEdge).varValue == null) edgeBuilder.append(String.format("         <data key=\"assumption\">%s.equals(%s)</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName, "\"\""));
                else edgeBuilder.append(String.format("         <data key=\"assumption\">%s.equals(%s)</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName,symbolicVariableInfoList.get(indexOfEdge).varValue));
            }
            else{
                if(symbolicVariableInfoList.get(indexOfEdge).varValue == null) edgeBuilder.append(String.format("         <data key=\"assumption\">%s==%s</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName, "\"\""));
                else edgeBuilder.append(String.format("         <data key=\"assumption\">%s==%s</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName, symbolicVariableInfoList.get(indexOfEdge).varValue));
            }
        }

        else{
            // Use == to follow standard graphml format
            if(symbolicVariableInfoList.get(indexOfEdge).varValue == null) edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %d</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName, 4));
            else edgeBuilder.append(String.format("         <data key=\"assumption\">%s == %d</data>\n", symbolicVariableInfoList.get(indexOfEdge).varName, symbolicVariableInfoList.get(indexOfEdge).varValue));
        }

        edgeBuilder.append(String.format("         <data key=\"assumption.scope\">java::L%s;</data>\n", assumptionScope));

        edgeBuilder.append("       </edge>\n");
        return edgeBuilder.toString();
    }

    public static String serializeAllEdges(List<Edge> edgeList){
        StringBuilder allEdgesBuilder = new StringBuilder();
        for(Edge edge : edgeList){
            allEdgesBuilder.append(edge.serializeEdge());
        }
        return allEdgesBuilder.toString();
    }

}
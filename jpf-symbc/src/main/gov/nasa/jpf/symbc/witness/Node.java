package gov.nasa.jpf.symbc.witness;

import java.util.List;


public class Node{
    public int numberOfNode;

    public int indexOfNode;
    public boolean noCounterExample;

    public String serializeNode(){
        // StringBuilder for serializing node of witness
        StringBuilder nodeBuilder = new StringBuilder(System.lineSeparator());
        // If there is no symbolic variable, generate empty witness
        if(numberOfNode == 0 || noCounterExample){
            nodeBuilder.append(String.format("       <node id=\"n%d\">\n", 0));
            nodeBuilder.append("           <data key=\"entry\">true</data> <data key=\"violation\">true</data>\n");
            nodeBuilder.append("       </node>");
            return nodeBuilder.toString();
        }

        nodeBuilder.append(String.format("       <node id=\"n%d\">\n", indexOfNode));
        if(indexOfNode == 0){
            nodeBuilder.append("             <data key=\"entry\">true</data>\n");
        }
        else if(indexOfNode == numberOfNode-1){
            nodeBuilder.append("             <data key=\"violation\">true</data>\n");
        }
        nodeBuilder.append("       </node>\n");
        return nodeBuilder.toString();
    }

    public static String serializeAllNodes(List<Node> nodeList){
        StringBuilder allNodesBuilder = new StringBuilder();
        for(Node node : nodeList){
            allNodesBuilder.append(node.serializeNode());
        }
        return allNodesBuilder.toString();
    }

    public Node(int numberOfNode, int indexOfNode, boolean noCounterExample){
        this.numberOfNode = numberOfNode;
        this.indexOfNode = indexOfNode;
        this.noCounterExample = noCounterExample;
    }

}
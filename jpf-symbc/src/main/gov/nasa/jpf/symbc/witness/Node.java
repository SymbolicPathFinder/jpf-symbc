/**
 * Object that represents a single node of the violation witness
 * It has two methods, serializeNode() and serializeAllNodes()
 * Variable numberOfNode denotes the total number of node of violation witness
 * Variable indexOfNode denotes the index of the node
 * Variable noCounterExample is a flag that shows whether the counterexample is exists or not
 */

package gov.nasa.jpf.symbc.witness;

import java.util.List;


public class Node{
    public int numberOfNode;

    public int indexOfNode;
    public boolean noCounterExample;

    public Node(int numberOfNode, int indexOfNode, boolean noCounterExample){
        this.numberOfNode = numberOfNode;
        this.indexOfNode = indexOfNode;
        this.noCounterExample = noCounterExample;
    }

    /**
     * It serializes a single node of violation witness
     * If there is no counterexample or the number of node is zero, it generates the node
     * that contains two keys, entry and violation
     * Else, it generates the node as String
     * @return A string that represents single node of violation witness
     */
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
        else if(indexOfNode == numberOfNode){
            nodeBuilder.append("             <data key=\"violation\">true</data>\n");
        }
        nodeBuilder.append("       </node>\n");
        return nodeBuilder.toString();
    }

    /**
     * It serializes every node in nodeList
     * @param nodeList contains all nodes of the violation witness
     * @return A string that represents every node of the violation witness
     */
    public static String serializeAllNodes(List<Node> nodeList){
        StringBuilder allNodesBuilder = new StringBuilder();
        for(Node node : nodeList){
            allNodesBuilder.append(node.serializeNode());
        }
        return allNodesBuilder.toString();
    }

}
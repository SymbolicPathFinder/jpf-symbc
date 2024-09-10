/**
 * Object that represents violation witness
 * It has 3 methods, constructHeader(), serializeWitness() and serializeEmptyWitness()
 * Two class variables are required : inputFilePath and outputFilePath
 * inputFilePath denotes the path to the witness template
 * outputFilePath denotes the path where the violation witness will exist
 */

package gov.nasa.jpf.symbc.witness;

import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.List;


public class GraphML{
        public InputStream inputStream;

        public String outputFilePath;

        public GraphML(InputStream inputStream, String outputFilePath){
            this.inputStream = inputStream;
            this.outputFilePath = outputFilePath;
        }

    /**
     * It reads witness template at inputFilePath
     * Then it assigns basic declaration of violation witness, such as key attribute declaration
     * to StringBuilder object
     * @return String consist of basic header information of violation witness(headers, witness type, producer name)
     */
    public String constructHeader(){
            StringBuilder header = new StringBuilder();
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream))){
                String line;
                while ((line = reader.readLine()) != null) {
                    header.append(line);
                    //System.out.println(line);
                    header.append(System.lineSeparator());
                }

            }catch (IOException e){
                System.out.println("IOException detected: " + e.getMessage());
                System.out.println("here");
            }
            return header.toString();
        }

    /**
     * Method that serializes violation witness based on 3 parameters
     * @param edgeList contains edges for violation witness
     * @param nodeList contains nodes for violation witness
     * @param header is the String that contains basic header information for violation witness
     */
        public void serializeWitness(List<Edge> edgeList, List<Node> nodeList, String header){
            try (FileWriter writer = new FileWriter(outputFilePath)){
                StringBuilder witnessBuilder = new StringBuilder();

                witnessBuilder.append(header);
                witnessBuilder.append(Node.serializeAllNodes(nodeList));
                witnessBuilder.append(Edge.serializeAllEdges(edgeList));

                witnessBuilder.append(System.lineSeparator() + "  </graph>" + System.lineSeparator());
                witnessBuilder.append("</graphml>" + System.lineSeparator());
                writer.write(witnessBuilder.toString());
            }catch (IOException e){
                System.out.println("IOException detected: " + e.getMessage());
            }
        }

    /**
     * Method that serializes empty violation witness
     * This method will be invoked when there is no counterexample or symbolic variable(invocation of Verifier.nondet~())
     * @param node represents the node for empty witness. It has two keys, which are entry and violation
     * that denotes start node of violation witness and represents the node that has violation, respectively.
     * @param header is the String that contains basic header information for violation witness
     */
    public void serializeEmptyWitness(String node, String header){
            try (FileWriter writer = new FileWriter(outputFilePath)){
                StringBuilder emptyWitnessBuilder = new StringBuilder();

                emptyWitnessBuilder.append(header);
                emptyWitnessBuilder.append(node);

                emptyWitnessBuilder.append(System.lineSeparator() + "  </graph>" + System.lineSeparator());
                emptyWitnessBuilder.append("</graphml>" + System.lineSeparator());
                writer.write(emptyWitnessBuilder.toString());
            }catch (IOException e){
                System.out.println("IOException detected: " + e.getMessage());
            }
        }
}



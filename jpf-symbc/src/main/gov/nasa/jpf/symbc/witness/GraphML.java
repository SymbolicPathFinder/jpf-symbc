package gov.nasa.jpf.symbc.witness;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;


public class GraphML{
        public String inputFilePath;

        public String outputFilePath;

        public GraphML(String inputFilePath, String outputFilePath){
            this.inputFilePath = inputFilePath;
            this.outputFilePath = outputFilePath;
        }

        public String constructHeader(){
            StringBuilder header = new StringBuilder();
            try (BufferedReader reader = new BufferedReader(new FileReader(inputFilePath))){
                String line;
                while ((line = reader.readLine()) != null) {
                    header.append(line);
                    header.append(System.lineSeparator());
                }

            }catch (IOException e){
                System.out.println("IOException detected: " + e.getMessage());
            }
            return header.toString();
        }

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



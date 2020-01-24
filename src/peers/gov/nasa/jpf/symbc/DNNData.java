package gov.nasa.jpf.symbc;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.File;
import java.io.IOException;

public class DNNData {

  public static double[][][][] weights0;
  public static double[][][][] weights2;
  public static double[][] weights6;
  public static double[][] weights8;
  
  public static double[] biases0;
  public static double[] biases2;
  public static double[] biases6;
  public static double[] biases8;
  
  public int d = 0;
  
  private DNNData(){}
  
  public static void main(String[] args) {
    // testing
    
    createFromDataFiles("./data");
    
    System.out.println("weights2");
    System.out.println(weights2[2][2][0][3]);
    
    System.out.println("Done.");
  }
  
  public static void createFromDataFiles(String path) {
    
    
    // Read biases0
    File fileBiases0 = new File(path + "/biases0.txt");
    biases0 = new double[2];
    try (BufferedReader br = new BufferedReader(new FileReader(fileBiases0))) {
      String line;
      int i=0;
      while ((line = br.readLine()) != null) {
        biases0[i] = Double.valueOf(line.trim());
        i++;
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    
    // Read biases2
    File fileBiases2 = new File(path + "/biases2.txt");
    biases2 = new double[4];
    try (BufferedReader br = new BufferedReader(new FileReader(fileBiases2))) {
      String line;
      int i=0;
      while ((line = br.readLine()) != null) {
        biases2[i] = Double.valueOf(line.trim());
        i++;
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    
    // Read biases6
    File fileBiases6 = new File(path + "/biases6.txt");
    biases6 = new double[128];
    try (BufferedReader br = new BufferedReader(new FileReader(fileBiases6))) {
      String line;
      int i=0;
      while ((line = br.readLine()) != null) {
        biases6[i] = Double.valueOf(line.trim());
        i++;
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    
    // Read biases8
    File fileBiases8 = new File(path + "/biases8.txt");
    biases8 = new double[10];
    try (BufferedReader br = new BufferedReader(new FileReader(fileBiases8))) {
      String line;
      int i=0;
      while ((line = br.readLine()) != null) {
        biases8[i] = Double.valueOf(line.trim());
        i++;
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    
    // Read weights0
    File fileWeights0 = new File(path + "/weights0.txt");
    weights0 = new double[3][3][1][2];
    try (BufferedReader br = new BufferedReader(new FileReader(fileWeights0))) {
      String line;
      for (int i=0; i<3; i++) {
        for (int j=0; j<3; j++) {
          for (int k=0; k<1; k++) {
            line = br.readLine();
            String[] items = line.split(",");
            for (int l=0; l<2; l++) {
              weights0[i][j][k][l] = Double.valueOf(items[l].trim());
            }
          }
        }
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    
    // Read weights2
    File fileWeights2 = new File(path + "/weights2.txt");
    weights2 = new double[3][3][2][4];
    try (BufferedReader br = new BufferedReader(new FileReader(fileWeights2))) {
      String line;
      for (int i=0; i<3; i++) {
        for (int j=0; j<3; j++) {
          for (int k=0; k<2; k++) {
            line = br.readLine();
            String[] items = line.split(",");
            for (int l=0; l<4; l++) {
              weights2[i][j][k][l] = Double.valueOf(items[l].trim());
            }
          }
        }
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    
    // Read weights6
    File fileWeights6 = new File(path + "/weights6.txt");
    weights6 = new double[576][128];
    try (BufferedReader br = new BufferedReader(new FileReader(fileWeights6))) {
      String line;
      int i=0;
      while ((line = br.readLine()) != null) {
        String[] items = line.split(",");
        for (int j=0; j<items.length; j++) {
          weights6[i][j] = Double.valueOf(items[j].trim());
        }
        i++;
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    
    // Read weights8
    File fileWeights8 = new File(path + "/weights8.txt");
    weights8 = new double[128][10];
    try (BufferedReader br = new BufferedReader(new FileReader(fileWeights8))) {
      String line;
      int i=0;
      while ((line = br.readLine()) != null) {
        String[] items = line.split(",");
        for (int j=0; j<items.length; j++) {
          weights8[i][j] = Double.valueOf(items[j].trim());
        }
        i++;
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    
  }
}
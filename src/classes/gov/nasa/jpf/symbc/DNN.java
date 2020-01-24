package gov.nasa.jpf.symbc;

//Methods to read the internal values of the DNN on the SPF side.
//needs to be generalized

public class DNN {
	native public static double get_biases0_value(int index);

    native public static double get_biases2_value(int index);

    native public static double get_biases6_value(int index);

    native public static double get_biases8_value(int index);

    native public static double get_weights6_value(int index0, int index1);

    native public static double get_weights8_value(int index0, int index1);

    native public static double get_weights0_value(int index0, int index1, int index2, int index3);

    native public static double get_weights2_value(int index0, int index1, int index2, int index3);

    public static double[] getBiases0() {
        double[] biases0 = new double[2];
        for (int i = 0; i < biases0.length; i++) {
            biases0[i] = get_biases0_value(i);
        }
        return biases0;
    }

    public static double[] getBiases2() {
        double[] biases2 = new double[4];
        for (int i = 0; i < biases2.length; i++) {
            biases2[i] = get_biases2_value(i);
        }
        return biases2;
    }

    public static double[] getBiases6() {
        double[] biases6 = new double[128];
        for (int i = 0; i < biases6.length; i++) {
            biases6[i] = get_biases6_value(i);
        }
        return biases6;
    }

    public static double[] getBiases8() {
        double[] biases8 = new double[10];
        for (int i = 0; i < biases8.length; i++) {
            biases8[i] = get_biases8_value(i);
        }
        return biases8;
    }

    public static double[][] getWeights6() {
        double[][] weights6 = new double[576][128];
        for (int i = 0; i < weights6.length; i++) {
            for (int j = 0; j < weights6[0].length; j++) {
                weights6[i][j] = get_weights6_value(i, j);
            }
        }
        return weights6;
    }

    public static double[][] getWeights8() {
        double[][] weights8 = new double[128][10];
        for (int i = 0; i < weights8.length; i++) {
            for (int j = 0; j < weights8[0].length; j++) {
                weights8[i][j] = get_weights8_value(i, j);
            }
        }
        return weights8;
    }

    public static double[][][][] getWeights0() {
        double[][][][] weights0 = new double[3][3][1][2];
        for (int i = 0; i < weights0.length; i++) {
            for (int j = 0; j < weights0[0].length; j++) {
                for (int k = 0; k < weights0[0][0].length; k++) {
                    for (int l = 0; l < weights0[0][0][0].length; l++) {
                        weights0[i][j][k][l] = get_weights0_value(i, j, k, l);
                    }
                }

            }
        }
        return weights0;
    }

    public static double[][][][] getWeights2() {
        double[][][][] weights2 = new double[3][3][2][4];
        for (int i = 0; i < weights2.length; i++) {
            for (int j = 0; j < weights2[0].length; j++) {
                for (int k = 0; k < weights2[0][0].length; k++) {
                    for (int l = 0; l < weights2[0][0][0].length; l++) {
                        weights2[i][j][k][l] = get_weights2_value(i, j, k, l);
                    }
                }

            }
        }
        return weights2;
    }
    
    native public static void readDataFromFiles(String path);
}

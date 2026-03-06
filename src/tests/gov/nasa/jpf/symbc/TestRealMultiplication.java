package gov.nasa.jpf.symbc;

public class TestRealMultiplication {

    public static void test(double x, double y) {
        double z = x * y;

        if (z == 10.0) {
            assert false;
        }
    }

    public static void main(String[] args) {
        test(0,0);
    }
}
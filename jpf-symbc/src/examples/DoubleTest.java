import gov.nasa.jpf.symbc.Debug;

public class DoubleTest {
    public static void main(String[] args) {
        double a = Debug.makeSymbolicReal("a");
        double b = Debug.makeSymbolicReal("b");
        test(a, b);
    }

    public static void test(double a, double b) {
        if(a > b) {
            if(a == Double.MAX_VALUE) {
                System.out.println("P001");
            }

            if(b == -Double.MAX_VALUE) {
                System.out.println("P002");
            }
        }

        if(a < 0 || b < 0) {
            System.out.println("F001");
        }
    }
}

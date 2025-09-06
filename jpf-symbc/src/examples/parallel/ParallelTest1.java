package parallel;

import gov.nasa.jpf.symbc.Debug;

public class ParallelTest1 {

    static int a;
    static int b;

    public static void main(String[] args) {
        int x = Debug.makeSymbolicInteger("x");
        a = Debug.makeSymbolicInteger("a");
        test(x, a, b);
    }

    public static void test(int x, int z, int r) {
        int y = 3;
        x = z + r;
        z = y * x;
        r = -z;
        if (x > 99) System.out.println("branch FOO1");
        else {
            assert false;
            System.out.println("branch FOO2");
        }
        if (r > z) System.out.println("branch BOO1");
        else System.out.println("branch BOO2");
    }
}

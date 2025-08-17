package solvers.z3;

import gov.nasa.jpf.symbc.Debug;

public class Z3TimeoutTest {
    public static void main(String[] args) {
        int size = Debug.makeSymbolicInteger("size");
        if (size < 2) {
            return;
        }
        args = new String[size];
        args[0] = Debug.makeSymbolicString("arg0");
        args[1] = Debug.makeSymbolicString("arg1");
        test(args[0], args[1]);
    }

    static void test(String a, String b) {
        try {
            int x = Integer.parseInt(a);
            int y = Integer.parseInt(b);
            assert Integer.parseInt(a) != Integer.parseInt(b) || x == y;
        } catch (java.lang.NumberFormatException e) {
        }
    }
}

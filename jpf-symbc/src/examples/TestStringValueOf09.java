import gov.nasa.jpf.symbc.Debug;

public class TestStringValueOf09 {

    public static void test() {
        String s = Debug.makeSymbolicString("s");

        double d = Double.parseDouble(s);
        String t = String.valueOf(d);

        if (s.equals("abc")) {
            assert false;
        }
    }

    public static void main(String[] args) {
        test();
    }
}
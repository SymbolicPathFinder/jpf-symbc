import gov.nasa.jpf.symbc.Debug;

public class TestDigitHandler {

    public static void testDigitHandler() {
        int radix = Debug.makeSymbolicInteger("radix");
        char c = Debug.makeSymbolicChar("c");
        if (radix < 2 || radix > 36) return;
        int d = Character.digit(c, radix);
        if (d == 5) {
            assert false;
        }
    }

    public static void main(String[] args) {
        testDigitHandler();
    }
}
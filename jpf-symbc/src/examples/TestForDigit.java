import gov.nasa.jpf.symbc.Debug;

public class TestForDigit {

    public static void testForDigit() {
         int radix = Debug.makeSymbolicInteger("radix");
        int digit = Debug.makeSymbolicInteger("digit");

        if (radix < 2 || radix > 36) return;
        if (digit < 0 || digit >= radix) return;

       char c = Character.forDigit(digit, radix);

        if (c == 0) {
            assert false;
        }
    }

    public static void main(String[] args) {
        testForDigit();
    }
}
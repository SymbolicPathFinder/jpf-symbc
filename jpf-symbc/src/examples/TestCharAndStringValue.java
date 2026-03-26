import gov.nasa.jpf.symbc.Debug;

public class TestCharAndStringValue {

    // Test for StaticCharMethods06
    public static void testGetNumericValue() {
        char c = Debug.makeSymbolicChar("c");

        //numeric behavior for digits
        int numeric = c - '0';

        //valid digit range
        if (c >= '0' && c <= '9') {
            if (numeric < 0 || numeric > 9) {
                assert false;
            }
        }
    }

    public static void main(String[] args) {
        testGetNumericValue();
    }
}
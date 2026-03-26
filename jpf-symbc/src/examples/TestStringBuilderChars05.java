import gov.nasa.jpf.symbc.Debug;

public class TestStringBuilderChars05 {

    public static void testSetCharAt() {
        String input = Debug.makeSymbolicString("input");

        StringBuilder builder = new StringBuilder(input);

        if (builder.length() > 6) {
            builder.setCharAt(0, 'H');
            builder.setCharAt(6, 'T');

            if (builder.charAt(0) == 'H' && builder.charAt(6) == 'T') {
                assert false;
            }
        }
    }

    public static void main(String[] args) {
        testSetCharAt();
    }
}
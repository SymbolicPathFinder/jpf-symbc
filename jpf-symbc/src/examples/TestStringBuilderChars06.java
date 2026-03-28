import gov.nasa.jpf.symbc.Debug;

public class TestStringBuilderChars06 {

    public static void testReverse() {
        String input = Debug.makeSymbolicString("input");

        StringBuilder buffer = new StringBuilder(input);

        buffer.reverse();

        if (input.length() > 0) {
            char first = input.charAt(0);
            char last = buffer.charAt(buffer.length() - 1);

            if (first == last) {
                assert false;
            }
        }
    }

    public static void main(String[] args) {
        testReverse();
    }
}
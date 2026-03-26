import gov.nasa.jpf.symbc.Debug;

public class TestStringBuilderCases {

    // ---- StringBuilderChars03 ----
    public static void testStringBuilderChars03() {
        String s = Debug.makeSymbolicString("s");

        StringBuilder sb = new StringBuilder(s);

        char c1 = sb.charAt(0);
        char c2 = sb.charAt(1);

        if (s.length() > 1 && c1 != c2) {
            assert false;
        }
    }
public static void main(String[] args) {
        testStringBuilderChars03();
    }
}
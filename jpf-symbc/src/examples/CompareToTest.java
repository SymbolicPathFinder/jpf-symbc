import gov.nasa.jpf.symbc.Debug;

public class CompareToTest {

    public static void main(String[] args) {

        String a = Debug.makeSymbolicString("a");
        String b = Debug.makeSymbolicString("b");

        int r = a.compareTo(b);

        if (r < 0) {
            assert false;
        }
    }
}
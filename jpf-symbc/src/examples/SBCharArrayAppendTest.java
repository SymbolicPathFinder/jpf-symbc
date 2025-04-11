import gov.nasa.jpf.symbc.Debug;

public class SBCharArrayAppendTest {

    public static void main(String[] args) {
        StringBuilder sb = new StringBuilder();
        String s = Debug.makeSymbolicString("s");
        char[] array = new char[3];
        array[0] = 'J';
        array[1] = 'P';
        array[2] = 'F';
        sb.append(s);
        sb.append(array);
        assert sb.toString().equals("JPF");
    }
}

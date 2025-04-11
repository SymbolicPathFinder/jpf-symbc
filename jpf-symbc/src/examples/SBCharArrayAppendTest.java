import gov.nasa.jpf.symbc.Debug;

public class SBCharArrayAppendTest {

    public static void main(String[] args) {
        if(test1()) {
            System.out.println("Test 1 passed");
        } else {
            System.out.println("Test 1 failed");
        }

        if(test2()) {
            System.out.println("Test 2 passed");
        } else {
            System.out.println("Test 2 failed");
        }

        if(test3()) {
            System.out.println("Test 3 passed");
        } else {
            System.out.println("Test 3 failed");
        }
    }

    //    Test case for symbolic StringBuilder and a concrete char array
    public static boolean test1() {
        StringBuilder sb = new StringBuilder();
        String s = Debug.makeSymbolicString("s");
        char[] array = new char[3];
        array[0] = 'J';
        array[1] = 'P';
        array[2] = 'F';
        sb.append(s);
        sb.append(array);
        return sb.toString().equals("JPF");
    }

    //    Test case for concrete StringBuilder and  symbolic char array
    public static boolean test2() {
        StringBuilder sb = new StringBuilder();
        String s = "JPF";
        char[] array = new char[3];
        array[0] = Debug.makeSymbolicChar("c1");
        array[1] = Debug.makeSymbolicChar("c2");
        array[2] = Debug.makeSymbolicChar("c3");
        sb.append(s);
        sb.append(array);
        return sb.toString().equals("JPF" + "abc");
    }

    //    Test case for symbolic StringBuilder and symbolic char array
    public static boolean test3() {
        StringBuilder sb = new StringBuilder();
        String s = Debug.makeSymbolicString("s1");
        char[] array = new char[3];
        array[0] = Debug.makeSymbolicChar("c1");
        array[1] = Debug.makeSymbolicChar("c2");
        array[2] = Debug.makeSymbolicChar("c3");
        sb.append(s);
        sb.append(array);
        return sb.toString().equals("JPF" + "abc");
    }

}

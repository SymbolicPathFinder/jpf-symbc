package veritesting;

public class TestAndIte extends TestRegionBaseClass {

//    public static int mwwTestAndIte(boolean x, boolean y) {
    public static Outputs mwwTestAndIte(boolean x, boolean y, int a) {
//        int a = 0;
        if (x && y) {
            a = a + 1;
        } else {
            a = a - 1;
        }
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = a+1;
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        TestAndIte s = new TestAndIte();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return mwwTestAndIte(b0, b1, in0);
    }
}

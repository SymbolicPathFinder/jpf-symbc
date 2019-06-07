package veritesting;

public class ArrayTest5 extends TestRegionBaseClass {

    public Outputs simpleRegion(boolean x, boolean y) {
        int[] b = {0,1};
        if (x) {
            b[0] = 3 + b[0];
        } else {
            b[0] = 2 + b[0];
        }
        if (y) {
            b[0] = 4 + b[0];
        } else {
            b[0] = 2 + b[0];
        }
        Outputs o = new Outputs();
        o.intOutputs = new int[2];
        o.intOutputs[0] = b[0];
        o.intOutputs[1] = b[1];
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        ArrayTest5 h = new ArrayTest5();
        t.runTest(h);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return simpleRegion(b0, b1);
    }
}
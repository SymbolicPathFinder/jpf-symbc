package veritesting;

public class HigherOrder2 extends TestRegionBaseClass {
    public static int staticMethod2(int x) {
        int myCount = 0;
        if (x != 100) {
            myCount = 1;
        } else {
            myCount = 3;
        }
        return myCount;
    }
    public static int staticMethod1(int x) {
        int myCount = 0;
        if (x != 10) {
            myCount = staticMethod2(x);
        } else {
            myCount = 2;
        }
        return myCount;
    }



    public Outputs simpleRegion(int x) {
        int val = -1;
        if (x != 0)
            val = staticMethod1(x );
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = val;
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        HigherOrder2 h = new HigherOrder2();
        t.runTest(h);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return simpleRegion(in0);
    }
}
package veritesting;

class Simple1 extends TestRegionBaseClass {

    Outputs simpleRegion(int x) {
        int count;
        if (x != 0) {
            count = 3;
        } else {
            count = 4;
        }
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = count+1;
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        Simple1 s = new Simple1();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return simpleRegion(in0);
    }
}
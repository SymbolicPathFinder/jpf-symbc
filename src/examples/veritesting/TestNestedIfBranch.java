package veritesting;

public class TestNestedIfBranch extends TestRegionBaseClass {

    public static Outputs mwwNestedIfBranch(int x, int y) {
        if (x < y) {
            if (y < 100) {
                y = 100;
            } else {
                y = y * 2;
            }
        } else {
            y = x;
        }
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = y+1;
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        TestNestedIfBranch s = new TestNestedIfBranch();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return mwwNestedIfBranch(in0, in1);
    }
}

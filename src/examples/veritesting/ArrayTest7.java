package veritesting;

public class ArrayTest7 extends TestRegionBaseClass {

    int u1resource, commUser, driveUser;
    public Outputs arrayTest(int in0, int in1, int in2) {
        u1resource = in0;
        commUser = 0;
        driveUser = 1;
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = Transition59_guard() ? 1 : 0;
        return o;
    }

    public boolean Transition59_guard() {
//        int commUser = 0, driveUser = 1;
        int resources[] = new int[]{0, 0};

        return u1resource == commUser
                && resources[(int) (commUser)] == 0
                && resources[(int) (driveUser)] == 0;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        ArrayTest7 s = new ArrayTest7();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return arrayTest(in0, in1, in2);
    }
}


package veritesting;

public class FieldTest1 extends TestRegionBaseClass {

    int count = 0;

    public Outputs fieldTest1(int x) {
        count = x;
        for (int i=0; i < 2; i++)
            if (count%2 != 0) count += 1;
//        assert( x != 0 ? count == 1 : true);
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = count;
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        FieldTest1 s = new FieldTest1();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return fieldTest1(in0);
    }
}

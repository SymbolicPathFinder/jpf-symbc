package veritesting;

public class ArrayTest2 extends TestRegionBaseClass {

    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                         boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5) {
        return arrayStore0(in0, in1);
    }

    public Outputs arrayStore0(int index, int length) {
        int[] x = {300, 400};
        int temp = 1;
//        try {
        if (index >= 0 && index < 2) {
            if (length <= 0) {
                temp = 2;
            } else {
                x[index] = temp + 2;
            }
        }
//        } catch (ArrayIndexOutOfBoundsException e) {
//            temp = 3;
//        }
//        assert length <= 0 ? temp == 2 : true;
//        assert length > 0 && index == 0 ? x[0] == 3 : true;
//        assert length > 0 && index == 1 ? x[1] == 3 : true;
//        assert length > 0 && index != 0 && index != 1 ? temp == 3 : true;
        Outputs o = new Outputs();
        o.intOutputs = new int[3];
        o.intOutputs[0] = x[0];
        o.intOutputs[1] = x[1];
        o.intOutputs[2] = temp+1;
        return o;
    }



    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        ArrayTest2 s = new ArrayTest2();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return arrayStore0(in0, in1);
    }
}
package veritesting;

public class HigherOrder3 extends TestRegionBaseClass {

    public Outputs simpleRegion(int x) {
        int val = -1;
        HO3Base ho3 = new HO3Derived();
        if (x != 0)
//            val += 1;
            val = ho3.method1(x );
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = val;
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        HigherOrder3 h = new HigherOrder3();
        t.runTest(h);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return simpleRegion(in0);
    }
}

class HO3Base {
    public int method2(int x) {
        int myCount = 0;
        if (x != 100) {
            myCount = 1;
        } else {
            myCount = 3;
        }
        return myCount;
    }
    public int method1(int x) {
//        int myCount = 0;
//        if (x != 10) {
//            myCount = method2(x);
//        } else {
//            myCount = 2;
//        }
//        return myCount;
        return 1;
    }
}

class HO3Derived extends HO3Base {
    public int method2(int x) {
        int myCount = 0;
        if (x != 100) {
            myCount = 3;
        } else {
            myCount = 1;
        }
        return myCount;
    }
    public int method1(int x) {
//        int myCount = 0;
//        if (x != 10) {
//            myCount = 2;
//        } else {
//            myCount = method2(x);
//        }
//        return myCount;
        return 2;
    }
}
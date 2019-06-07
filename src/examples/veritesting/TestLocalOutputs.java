package veritesting;

public class TestLocalOutputs extends TestRegionBaseClass {

    static int patParaIndex = 0;
    static int patIndex = 0;

    public static Outputs makepat(int _patParaIndex, int _patIndex, int _lastj) {
        int lastj = _lastj; // stack slot = 3
        int lj = _patIndex; // stack slot = 4
        boolean done = false; // stack slot = 5
//        patIndex = _patIndex;
        char[] pat = {'a', 'b'}; // stack slot = 6
        patParaIndex = _patParaIndex;
        if(patParaIndex > 0){
//            _lastj++; // stack slot = 2
//            lastj++; // stack slot = 3
            lj = lastj; // stack slot = 4
            if (lj >= 0 && lj < 2) {
//                char tempChar = pat[lj]; // stack slot = 7
//                if (pat[lj] == 'a') {
//                    done = true;
//                }
            }
        }
        else{
//            lj++;
        }
        Outputs o = new Outputs();
        o.intOutputs = new int[3];
        o.intOutputs[0] = lj;
        o.intOutputs[1] = lastj;
        o.intOutputs[2] = (done ? 1 : 0);
        return o;
    }


    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        TestLocalOutputs s = new TestLocalOutputs();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return makepat(in0, in1, in2);
    }
}


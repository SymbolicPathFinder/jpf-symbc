package veritesting;

public class EqSPFCasesTest2 extends TestRegionBaseClass {

    int count = 0;

    public Outputs createObjectTC8(boolean x, boolean y) {

            int a = 0;
            if (y) {
                if (x) {
                    a = 3 + a;
                } else {
                    a = 2 + a;
                }
            } else {
                if (x) {
                    a = 4 + a ;
                    TempClass tempClass2 = new TempClass();
                } else {
                    TempClass tempClass2 = new TempClass();
                    a = 5 + a;
                }
            }
        /*assert((y && x) ? a==3: true);
        assert((y && !x) ? a==2: true);
        assert(!y & x ? a==4: true);
        assert(!y & !x ? a==5: true);
*/
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = a;
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        EqSPFCasesTest2 s = new EqSPFCasesTest2();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return createObjectTC8(b0, b1);
    }
}

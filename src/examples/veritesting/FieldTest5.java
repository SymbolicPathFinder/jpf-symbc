package veritesting;

public class FieldTest5 extends TestRegionBaseClass {

    int count = 0;

    public Outputs fieldTest5(int x) {
        Cur_Vertical_Sep = x;
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = alt_sep_test();
        return o;
    }
    public static int Cur_Vertical_Sep;
    public static int UNRESOLVED = 0;
    public static int MAXALTDIFF = 300;

    public int alt_sep_test() {
        int alt_sep = UNRESOLVED;
        if(Cur_Vertical_Sep > MAXALTDIFF){
            alt_sep = UNRESOLVED; // alt_assign();
        }
        return alt_sep;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        FieldTest5 s = new FieldTest5();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return fieldTest5(in0);
    }
}


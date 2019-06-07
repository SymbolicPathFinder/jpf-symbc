package veritesting;

public class ArrayTest6 extends TestRegionBaseClass {

    static int patParaIndex = 0;
    static int patIndex = 0;
    static int patLen = 1;

    // taken from replace.getccl and modified to have local, field, and an array with outputs
    public Outputs replace_GetCCL(char c0, char c1, int i0, int i1) {
        patParaIndex = 0;
        patIndex = i1;
//        patIndex = 0;
        patLen = 2;
        char arg[] = {c0, c1};
        char pat[] = new char[2];
        char local = ' ';

        if(arg[patParaIndex] == '^') {
            if(patIndex >= 0 && patIndex < patLen) {
                local = pat[patIndex];
                pat[patIndex] = '!';
                local = pat[patIndex];
                patIndex = patIndex + 1;
            }
            patParaIndex = patParaIndex + 1;
        } else {
            if(patIndex >= 0 && patIndex < patLen){
                local = pat[patIndex];
                pat[patIndex] = '[';
                local = pat[patIndex];
                patIndex = patIndex + 1;
            }
        }
        return new Outputs(new int[]{patIndex, patParaIndex, pat[0], pat[1], local, arg[0], arg[1]});
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        ArrayTest6 h = new ArrayTest6();
        t.runTest(h);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                         boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5,
                         char c0, char c1, char c2, char c3, char c4, char c5) {
        return replace_GetCCL(c0, c1, in0, in1);
    }
}
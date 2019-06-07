package veritesting;

public class ArrayTest4  extends TestRegionBaseClass {

    public static final int patParaLen = 3;
    public static int patParaIndex = 0;
    public static final int patLen = 10;
    public static int patIndex = 0;

    public static final int subParaLen = 3;
    public static int subParaIndex = 0;
    public static final int subLen = 10;
    public static int subIndex = 0;

    public static final int strLen = 2;
    public static int strIndex = 0;
    public static int tempIndex = 0;
    //
//	public static int strIndex = 0;

    public static final char ENDSTR = '\0';
    public static final char ESCAPE = '@';
    public static final char CLOSURE = '*';
    public static final char BOL = '%';
    public static final char EOL = '$';
    public static final char ANY = '?';
    public static final char CCL = '[';
    public static final char CCLEND = ']';
    public static final char NEGATE = '^';
    public static final char NCCL = '!';
    public static final char LITCHAR = 'c';
    public static final char DASH = '-';

    public static final int DITTO = -1;
    public static final int TAB = 9;
    public static final int NEWLINE = 10;
    public static final int CLOSIZE = 1;

    public static void reset() {
        patParaIndex = 0;
        patIndex = 0;
        subParaIndex = 0;
        subIndex = 0;
        strIndex = 0;
        tempIndex = 0;
    }

    public static char[] mainProcess(char i2, char i3){

        char[] subPara = new char[subParaLen];
        subPara[0] = i2;
        subPara[1] = i3;
        subPara[2] = '\0';
        char[] sub = new char[subLen];
        int subResult = makesub(subPara, sub);
        char[] retChar = new char[sub.length];
        for (int i = 0; i < sub.length; i++)
            retChar[i] = sub[i];
        return retChar;
    }

    private static int makesub(char[] arg, char[] sub) {
        if(arg[subParaIndex] == '&'){
            char ch = (char)DITTO;
            if(subIndex < subLen){
                sub[subIndex] = ch;
            }
        }
        return 0;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        ArrayTest4 s = new ArrayTest4();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                         boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5,
                         char c0, char c1, char c2, char c3, char c4, char c5) {
        return new Outputs(mainProcess(c0, c1));
    }
}
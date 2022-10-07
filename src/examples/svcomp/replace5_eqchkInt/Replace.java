package svcomp.replace5_eqchkInt;

public class Replace {

//    public static int patParaIndex = 0;
    public static final char ENDSTR = '\0';
    public static final char ANY = '?';
    public static final char CCL = '[';
    public static final char CCLEND = ']';
    public static final char NEGATE = '^';


    static char[] printBuf;


    public static int[] mainProcess(int i0, int i1) {
        int patParaIndex = 0;
        printBuf = new char[50];

        int[] patPara = new int[3];
        patPara[0] = i0;
        patPara[1] = i1;
        patPara[2] = '\0';
        boolean done = false;
        boolean continueIndex = false;

        if (patPara[patParaIndex] != ENDSTR) //T
            continueIndex = true;

        while (continueIndex) { //T
            //main region
            if (patPara[patParaIndex] == CCL) { //T
                patParaIndex = patParaIndex + 1;
//                assert patParaIndex < 3;
                if (patPara[patParaIndex] == NEGATE) //JR
                    patParaIndex = patParaIndex + 1; //field output patParaIndex
                boolean getres = patPara[patParaIndex] == CCLEND; //F
                done = (!getres); //local output done
            }

            continueIndex = false;

            if (!done) {
                patParaIndex = patParaIndex + 1;
                if (patPara[patParaIndex] != ENDSTR)
                    continueIndex = true;
            }
        }
        return new int[]{};
    }
}
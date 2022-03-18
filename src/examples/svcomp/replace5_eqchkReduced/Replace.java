package svcomp.replace5_eqchkReduced;

public class Replace {

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

    public static final int printBufLen = 50;
    static int printBufIdx = 0;
    static char[] printBuf;

    public static void reset() {
        patParaIndex = 0;
        patIndex = 0;
        subParaIndex = 0;
        subIndex = 0;
        strIndex = 0;
        tempIndex = 0;
        printBufIdx = 0;
    }

    public static char[] mainProcess(char i0, char i1, char i2, char i3, char i4) {
        printBuf = new char[printBufLen];

        char[] patPara = new char[patParaLen];
        patPara[0] = i0;
        patPara[1] = i1;

        patPara[2] = '\0';
        char[] pat = new char[patLen];
        int patResult = makepat(patPara, pat);

        return new char[]{};
    }


    public static int makepat(char[] arg, char[] pat) {
        int lastj = 0;
        boolean done = false;
        boolean continueIndex = false;
        if (arg[patParaIndex] != ENDSTR) {
            continueIndex = true;
        }

        while (continueIndex) {
            int lj = patIndex;
            if (arg[patParaIndex] == CCL) {
                boolean getres = getccl(arg, pat);

                if (!getres) {
                    done = true;
                } else {
                    done = false;
                }
            } else {
                char escjunk = ' ';
//                if (patIndex < patLen) {
//                    pat[patIndex] = escjunk;
//                    patIndex = patIndex + 1;
//                }

            }
            continueIndex = false;
            if (!done) {
                patParaIndex = patParaIndex + 1;
                if (arg[patParaIndex] != ENDSTR) {
                    continueIndex = true;
                }
            }
        }

        return 1;
    }


    public static boolean getccl(char[] arg, char[] pat) {
        patParaIndex = patParaIndex + 1;
        if (arg[patParaIndex] == NEGATE) {
            if (patIndex < patLen) {
                pat[patIndex] = NCCL;
                patIndex = patIndex + 1;
            }
            patParaIndex = patParaIndex + 1;
        } //add this after solving the crash
//        else {
//            if (patIndex < patLen) {
//                pat[patIndex] = CCL;
//                patIndex = patIndex + 1;
//            }
//        }

        int jstart = patIndex;


        dodash(CCLEND, arg, pat);

        char _jstart = (char) (patIndex - jstart - 1);
        pat[jstart] = _jstart;
        if (arg[patParaIndex] == CCLEND) {
            return true;
        } else {
            return false;
        }
    }

    public static void dodash(char delim, char[] src, char[] dest) {

        boolean continueIndex = false;
        if (src[patParaIndex] != delim) {
            if (src[patParaIndex] != ENDSTR) {
                continueIndex = true;
            }
        }
        while (continueIndex) {
            if (src[patParaIndex] != DASH) {
                if (patIndex < patLen) {
                    dest[patIndex] = src[patParaIndex];
                    patIndex = patIndex + 1;
                }
            } else {

                if (patIndex < patLen) {
                    dest[patIndex] = DASH;
                    patIndex = patIndex + 1;
                }
            }
            patParaIndex = patParaIndex + 1;
            continueIndex = false;
            if (src[patParaIndex] != delim) {
                if (src[patParaIndex] != ENDSTR) {
                    continueIndex = true;
                }
            }
        }
    }

}

package veritesting;

public class EqSPFCasesTest1 extends TestRegionBaseClass {

    int count = 0;

    public Outputs createObjectTC8(boolean x, boolean y) {
        int a = 0;
        if (x) {
            a = 3 + a;
        } else {
            if (y) a = 1 + a;
            else { a = 2 + a;
            TempClass tempClass2 = new TempClass();}
        }

        if (y) {
            a = 4 + a;
        } else {
            a = 2 + a;
        }
      Outputs o = new Outputs();
        o.intOutputs = new int[]{a};
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        EqSPFCasesTest1 s = new EqSPFCasesTest1();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return createObjectTC8(b0, b1);
    }
}

class TempClass {

    public static int tempInt = 1;

    public static int myInt = 1;

    public TempClass() {
        this.tempClass2 = new TempClass2();
    }

    public int getTempInt() {
        return tempInt;
    }

    public int getOne(int a) {
        System.out.println("called TempClass.getOne");
        tempInt = a;
        return tempInt;
    }

    TempClass2 tempClass2;

    public int nestedRegion(int a) {
        return 0;
    }
}

class TempClass2 {

    public int tempInt2 = 1;

    public int tempMethod() {
        return 0;
    }
}

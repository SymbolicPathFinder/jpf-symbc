package veritesting;

public class FieldTest6 extends TestRegionBaseClass {

    int count = 0;
    boolean startBtn0, launchBtn0, startBtn1, launchBtn1;

    public Outputs fieldTest(boolean b0, boolean b1, boolean b2, boolean b3) {
        startBtn0 = b0;
        launchBtn0 = b1;
        startBtn1 = b2;
        launchBtn1 = b3;
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = getCurrentState();
        return o;
    }

    public int getCurrentState() {
        int padState;
        boolean mystartBtn = this.startBtn0;
        boolean myLaunchBtn = this.launchBtn0;

        if (!this.startBtn0 && !this.launchBtn0) { //IDLE State
            if (!this.startBtn1 && !this.launchBtn1)  //IDLE State
                padState = 0;
            else padState = 2;
        }
        else
            padState = -1; // Invalid State
        return padState;
    }

    public int getCurrentState1() {
        int padState = 2;
        boolean mystartBtn = this.startBtn0;
        boolean myLaunchBtn = this.launchBtn0;

        if (this.startBtn0) {
            this.count = 1;
            if (!this.launchBtn0) {
                padState = 0;
            }
        }
        else {
//            padState = -1; // Invalid State
            this.count = 2;
            if (!this.launchBtn0) {
                padState = -1;
            }
        }
        return padState;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        FieldTest6 s = new FieldTest6();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5, boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5, char c0, char c1, char c2, char c3, char c4, char c5) {
        return fieldTest(b0, b1, b2, b3);
    }
}


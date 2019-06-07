package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;


public class FailEntry {
    public enum FailReason {
        FIELDREFERNCEINSTRUCTION,
        SPFCASEINSTRUCTION,
        CONCRETE,
        MISSINGMETHODSUMMARY,
        OTHER;
    }

    public FailReason failReason;
    public String failMsg;


    public FailEntry(FailReason failReason, String failMsg){
        this.failReason = failReason;
        this.failMsg = failMsg;
    }

    @Override
    public String toString() {
        return super.toString() + (this.failMsg == "" ? "" : " - FailInstruction = " + this.failMsg.toString());
    }
}
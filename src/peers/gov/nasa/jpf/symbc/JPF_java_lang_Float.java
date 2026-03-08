package gov.nasa.jpf.symbc;

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;

// Peer for Float.parseFloat(String) to support symbolic execution
public class JPF_java_lang_Float extends NativePeer {

    @MJI
    public float parseFloat__Ljava_lang_String_2__F(MJIEnv env, int clsRef, int strRef) {

        SymbolicReal sym = new SymbolicReal("sym_float");

        env.setReturnAttribute(sym);

        return 0.0f;
    }
}
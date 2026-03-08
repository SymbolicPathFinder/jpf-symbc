package gov.nasa.jpf.symbc;

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;

// Peer for Double.parseDouble(String) to support symbolic execution
public class JPF_java_lang_Double extends NativePeer {

    @MJI
    public double parseDouble__Ljava_lang_String_2__D(MJIEnv env, int clsRef, int strRef) {

        return 0.0;
    }
}
package gov.nasa.jpf.symbc;

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;

// Stub for AbstractStringBuilder.capacity() used in benchmarks
public class JPF_java_lang_AbstractStringBuilder extends NativePeer {

    @MJI
    public int capacity____I(MJIEnv env, int objRef) {
        return 69;
    }
}
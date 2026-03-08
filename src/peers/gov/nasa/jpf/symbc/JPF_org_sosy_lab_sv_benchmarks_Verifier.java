package gov.nasa.jpf.symbc;

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;

public class JPF_org_sosy_lab_sv_benchmarks_Verifier extends NativePeer {

    @MJI
    public int nondetString____Ljava_lang_String_2(MJIEnv env, int clsRef) {

        int ref = env.newString("");

        StringSymbolic sym = new StringSymbolic("sym_nondet_string");

        env.setObjectAttr(ref, sym);

        return ref;
    }
}
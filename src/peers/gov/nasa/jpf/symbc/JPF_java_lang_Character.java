package gov.nasa.jpf.symbc;

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;
// Peer implementations for Character API methods used during symbolic execution
public class JPF_java_lang_Character extends NativePeer {

    @MJI
    public boolean isDefined__C__Z(MJIEnv env, int clsObjRef, int c) {
        Object[] attrs = env.getArgAttributes();
        Object attr = (attrs != null) ? attrs[0] : null;

        if (attr == null) {
            return Character.isDefined((char) c);
        }

        SymbolicInteger sym = new SymbolicInteger("isDefined_" + attr);
        env.setReturnAttribute(sym);

        return false;
    }

    @MJI
    public int digit__CI__I(MJIEnv env, int clsObjRef, int ch, int radix) {

        Object[] attrs = env.getArgAttributes();

        if (attrs == null || (attrs[0] == null && attrs[1] == null)) {
            return Character.digit((char) ch, radix);
        }

        SymbolicInteger symResult =
                new SymbolicInteger("digit_" + ch, -1, 35);

        int result = Character.digit((char) ch, radix);
        env.setReturnAttribute(symResult);
        return result;
    }

    @MJI
    public char forDigit__II__C(MJIEnv env, int clsObjRef, int digit, int radix) {

        Object[] attrs = env.getArgAttributes();

        if (attrs == null || (attrs[0] == null && attrs[1] == null)) {
            return Character.forDigit(digit, radix);
        }

        SymbolicInteger symResult =
                new SymbolicInteger("forDigit_" + digit + "_" + radix, 0, 65535);

        char result = Character.forDigit(digit, radix);
        env.setReturnAttribute(symResult);
        return result;
    }
}
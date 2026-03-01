package gov.nasa.jpf.symbc;

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;

public class JPF_java_lang_Character extends NativePeer {

   @MJI
    public boolean isDefined__C__Z (MJIEnv env, int clsObjRef, int c) {
        Object[] attrs = env.getArgAttributes();
        if (attrs == null || attrs[0] == null) {
            return Character.isDefined((char) c);
        }

        SymbolicInteger symResult = new SymbolicInteger("isDefined_" + attrs[0].toString(), 0, 1);
        env.setReturnAttribute(symResult);
        return false; 
    }
}
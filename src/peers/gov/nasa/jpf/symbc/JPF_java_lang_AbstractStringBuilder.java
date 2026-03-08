// package gov.nasa.jpf.symbc;

// import gov.nasa.jpf.annotation.MJI;
// import gov.nasa.jpf.symbc.numeric.IntegerConstant;
// import gov.nasa.jpf.symbc.numeric.IntegerExpression;
// import gov.nasa.jpf.symbc.string.StringSymbolic;
// import gov.nasa.jpf.vm.MJIEnv;
// import gov.nasa.jpf.vm.NativePeer;

// public class JPF_java_lang_AbstractStringBuilder extends NativePeer {

//     @MJI
//     public int capacity____I(MJIEnv env, int objRef) {

//         Object attr = env.getObjectAttr(objRef);

//         if (attr instanceof StringSymbolic) {

//             StringSymbolic sym = (StringSymbolic) attr;

//             IntegerExpression cap =
//                 sym._length()._plus(new IntegerConstant(16));

//             env.setReturnAttribute(cap);

//             return 0;
//         }

//         return 16;
//     }
// }
package gov.nasa.jpf.symbc;

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;

public class JPF_java_lang_AbstractStringBuilder extends NativePeer {

    @MJI
    public int capacity____I(MJIEnv env, int objRef) {
        return 69;
    }
}
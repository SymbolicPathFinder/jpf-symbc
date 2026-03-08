    package gov.nasa.jpf.symbc;

    import gov.nasa.jpf.annotation.MJI;
    import gov.nasa.jpf.vm.MJIEnv;
    import gov.nasa.jpf.vm.NativePeer;
    import gov.nasa.jpf.vm.ElementInfo;

    public class JPF_java_lang_StringBuilder extends NativePeer {

        /**
         * StringBuilder(String)
         */
    @MJI
    public void $init__Ljava_lang_String_2__V(MJIEnv env, int objRef, int strRef) {

        if (strRef == MJIEnv.NULL) {
            return;
        }

        // propagate symbolic attribute from String to StringBuilder
        Object attr = env.getObjectAttr(strRef);

        if (attr != null) {
            env.setObjectAttr(objRef, attr);
        }
    }
        /**
         * capacity()
         * Java rule: capacity = length + 16
         */
    // @MJI
    // public int capacity____I(MJIEnv env, int objRef) {

    //     Object attr = env.getObjectAttr(objRef);

    //     if (attr instanceof gov.nasa.jpf.symbc.string.StringSymbolic) {

    //         gov.nasa.jpf.symbc.string.StringSymbolic sym =
    //             (gov.nasa.jpf.symbc.string.StringSymbolic) attr;

    //         gov.nasa.jpf.symbc.numeric.IntegerExpression cap =
    //             sym._length._plus(16);

    //         env.setReturnAttribute(cap);

    //         return 0; // concrete placeholder
    //     }

    //     return 16;
    // }

        /**
         * length()
         */
        @MJI
        public int length____I(MJIEnv env, int objRef) {

            ElementInfo ei = env.getElementInfo(objRef);

            int valueRef = ei.getReferenceField("value");

            if (valueRef == MJIEnv.NULL) {
                return 0;
            }

            String str = env.getStringObject(valueRef);

            return str.length();
        }
    }
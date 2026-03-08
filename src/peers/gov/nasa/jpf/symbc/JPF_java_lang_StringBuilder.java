    package gov.nasa.jpf.symbc;

    import gov.nasa.jpf.annotation.MJI;
    import gov.nasa.jpf.vm.MJIEnv;
    import gov.nasa.jpf.vm.NativePeer;
    import gov.nasa.jpf.vm.ElementInfo;
// Peer implementations for basic StringBuilder operations used in symbolic execution
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
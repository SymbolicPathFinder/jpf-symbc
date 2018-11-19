/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */

package gov.nasa.jpf.symbc;

import java.util.HashSet;
import java.util.Set;

import gov.nasa.jpf.annotation.MJI;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.MinMax;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.NativePeer;
import gov.nasa.jpf.vm.ReferenceFieldInfo;
import gov.nasa.jpf.vm.StaticElementInfo;
import gov.nasa.jpf.vm.SystemState;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

public class JPF_gov_nasa_jpf_symbc_Debug extends NativePeer {

    @MJI
    public static PathCondition getPC(MJIEnv env) {
        VM vm = env.getVM();
        ChoiceGenerator<?> cg = vm.getChoiceGenerator();
        PathCondition pc = null;

        if (!(cg instanceof PCChoiceGenerator)) {
            ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
            while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
                prev_cg = prev_cg.getPreviousChoiceGenerator();
            }
            cg = prev_cg;
        }

        if ((cg instanceof PCChoiceGenerator) && cg != null) {
            pc = ((PCChoiceGenerator) cg).getCurrentPC();
        }
        return pc;
    }

    @MJI
    public static void printPC(MJIEnv env, int objRef, int msgRef) {
        PathCondition pc = getPC(env);
        if (pc != null) {
            // pc.solve();
            System.out.println(env.getStringObject(msgRef) + pc);
        } else
            System.out.println(env.getStringObject(msgRef) + " PC is null");
    }

    @MJI
    public static int getSolvedPC(MJIEnv env, int objRef) {
        PathCondition pc = getPC(env);
        if (pc != null) {
            pc.solve();
            return env.newString(pc.toString());
        }
        return env.newString("");
    }

    @MJI
    public static int getPC_prefix_notation(MJIEnv env, int objRef) {
        PathCondition pc = getPC(env);
        if (pc != null) {
            pc.solve();
            return env.newString(pc.prefix_notation());
        }
        return env.newString("");
    }

    @MJI
    public static int getSymbolicIntegerValue(MJIEnv env, int objRef, int v) {
        Object[] attrs = env.getArgAttributes();

        IntegerExpression sym_arg = (IntegerExpression) attrs[0];
        if (sym_arg != null)
            return env.newString(sym_arg.toString());
        else
            return env.newString(Long.toString(v));
    }

    @MJI
    public static int getSymbolicByteValue(MJIEnv env, int objRef, byte v) {
        Object[] attrs = env.getArgAttributes();

        IntegerExpression sym_arg = (IntegerExpression) attrs[0];
        if (sym_arg != null)
            return env.newString(sym_arg.toString());
        else
            return env.newString(Long.toString(v));
    }

    @MJI
    public static int getSymbolicLongValue(MJIEnv env, int objRef, long v) {
        Object[] attrs = env.getArgAttributes();

        IntegerExpression sym_arg = (IntegerExpression) attrs[0];
        if (sym_arg != null)
            return env.newString(sym_arg.toString());
        else
            return env.newString(Long.toString(v));
    }

    @MJI
    public static boolean isSymbolicInteger(MJIEnv env, int objRef, int v) {
        Object[] attrs = env.getArgAttributes();
        if (attrs != null) {
            IntegerExpression sym_arg = (IntegerExpression) attrs[0];
            if (sym_arg != null)
                return true;
        }
        return false;
    }

    @MJI
    public static boolean isSymbolicLong(MJIEnv env, int objRef, long v) {
        Object[] attrs = env.getArgAttributes();
        if (attrs != null) {
            IntegerExpression sym_arg = (IntegerExpression) attrs[0];
            if (sym_arg != null)
                return true;
        }
        return false;
    }

    @MJI
    public static boolean isSymbolicShort(MJIEnv env, int objRef, short v) {
        Object[] attrs = env.getArgAttributes();
        if (attrs != null) {
            IntegerExpression sym_arg = (IntegerExpression) attrs[0];
            if (sym_arg != null)
                return true;
        }
        return false;
    }

    @MJI
    public static boolean isSymbolicByte(MJIEnv env, int objRef, byte v) {
        Object[] attrs = env.getArgAttributes();
        if (attrs != null) {
            IntegerExpression sym_arg = (IntegerExpression) attrs[0];
            if (sym_arg != null)
                return true;
        }
        return false;
    }

    @MJI
    public static boolean isSymbolicChar(MJIEnv env, int objRef, char v) {
        Object[] attrs = env.getArgAttributes();
        if (attrs != null) {
            IntegerExpression sym_arg = (IntegerExpression) attrs[0];
            if (sym_arg != null)
                return true;
        }
        return false;
    }

    @MJI
    public static int getSymbolicRealValue(MJIEnv env, int objRef, double v) {
        Object[] attrs = env.getArgAttributes();
        RealExpression sym_arg = (RealExpression) attrs[0];
        if (sym_arg != null)
            return env.newString(sym_arg.toString());
        else
            return env.newString(Double.toString(v));
    }

    @MJI
    public static int getSymbolicBooleanValue(MJIEnv env, int objRef, boolean v) {
        Object[] attrs = env.getArgAttributes();
        IntegerExpression sym_arg = (IntegerExpression) attrs[0];
        if (sym_arg != null)
            return env.newString(sym_arg.toString());
        else
            return env.newString(Boolean.toString(v));
    }

    @MJI
    public static int getSymbolicStringValue(MJIEnv env, int objRef, int stringRef) {
        Object[] attrs = env.getArgAttributes();
        StringExpression sym_arg = (StringExpression) attrs[0];
        String string_concrete = env.getStringObject(stringRef);
        if (sym_arg != null)
            return env.newString(sym_arg.toString());
        else
            return env.newString(string_concrete);
    }

    @MJI
    public static void assume(MJIEnv env, int objRef, boolean c) {
        Object[] attrs = env.getArgAttributes();
        if (attrs == null)
            return;
        IntegerExpression sym_arg = (IntegerExpression) attrs[0];
        assert (sym_arg == null);
        if (!c) {// instruct JPF to backtrack
            SystemState ss = env.getSystemState();
            ss.setIgnored(true);
        }
    }

    @MJI
    public static byte addSymbolicByte(MJIEnv env, int objRef, byte v, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicInteger(name, MinMax.getVarMinByte(name), MinMax.getVarMaxByte(name)));
        return v;
    }

    @MJI
    public static char addSymbolicChar(MJIEnv env, int objRef, char v, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicInteger(name, MinMax.getVarMinByte(name), MinMax.getVarMaxByte(name)));
        return v;
    }

    @MJI
    public static int addSymbolicInt(MJIEnv env, int objRef, int v, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicInteger(name, MinMax.getVarMinInt(name), MinMax.getVarMaxInt(name)));
        return v;
    }
    
    @MJI
    public static double addSymbolicDouble(MJIEnv env, int objRef, double v, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicReal(name));//, MinMax.getVarMinDouble(name), MinMax.getVarMaxDouble(name))); Corina: to check
        return v;
    }
    
    @MJI
    public static int makeSymbolicInteger(MJIEnv env, int objRef, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicInteger(name, MinMax.getVarMinInt(name), MinMax.getVarMaxInt(name)));
        return 0;
    }

    @MJI
    public static long makeSymbolicLong(MJIEnv env, int objRef, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicInteger(name, MinMax.getVarMinLong(name), MinMax.getVarMaxLong(name)));
        return 0;
    }

    @MJI
    public static short makeSymbolicShort(MJIEnv env, int objRef, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicInteger(name, MinMax.getVarMinShort(name), MinMax.getVarMaxShort(name)));
        return 0;
    }

    @MJI
    public static byte makeSymbolicByte(MJIEnv env, int objRef, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicInteger(name, MinMax.getVarMinByte(name), MinMax.getVarMaxByte(name)));
        return 0;
    }

    @MJI
    public static char makeSymbolicChar(MJIEnv env, int objRef, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicInteger(name, MinMax.getVarMinChar(name), MinMax.getVarMaxChar(name)));
        return 0;
    }

    @MJI
    public static double makeSymbolicReal(MJIEnv env, int objRef, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicReal(name, MinMax.getVarMinDouble(name), MinMax.getVarMaxDouble(name)));
        return 0.0;
    }

    @MJI
    public static boolean makeSymbolicBoolean(MJIEnv env, int objRef, int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new SymbolicInteger(name, 0, 1));
        return false;
    }

    @MJI
    public static int makeSymbolicString__Ljava_lang_String_2__Ljava_lang_String_2(MJIEnv env, int objRef,
            int stringRef) {
        String name = env.getStringObject(stringRef);
        env.setReturnAttribute(new StringSymbolic(name));
        return env.newString("WWWWW's Birthday is 12-17-77");
    }

    // public static int makeSymbolicRef(MJIEnv env, int objRef, int stringRef, int objvRef) {
    // String name = env.getStringObject(stringRef);
    // env.setReturnAttribute(new SymbolicInteger(name,0,1));
    // return objvRef;
    // }

    // the purpose of this method is to set the PCheap to the "eq null" constraint for the input specified w/ stringRef
    @MJI
    public static int makeSymbolicNull(MJIEnv env, int objRef, int stringRef) {

        // introduce a heap choice generator for the element in the heap
        ThreadInfo ti = env.getVM().getCurrentThread();
        SystemState ss = env.getVM().getSystemState();
        ChoiceGenerator<?> cg;

        if (!ti.isFirstStepInsn()) {
            cg = new HeapChoiceGenerator(1); // new
            ss.setNextChoiceGenerator(cg);
            env.repeatInvocation();
            return MJIEnv.NULL; // not used anyways
        }
        // else this is what really returns results

        cg = ss.getChoiceGenerator();
        assert (cg instanceof HeapChoiceGenerator) : "expected HeapChoiceGenerator, got: " + cg;

        // see if there were more inputs added before
        ChoiceGenerator<?> prevHeapCG = cg.getPreviousChoiceGenerator();
        while (!((prevHeapCG == null) || (prevHeapCG instanceof HeapChoiceGenerator))) {
            prevHeapCG = prevHeapCG.getPreviousChoiceGenerator();
        }

        PathCondition pcHeap;
        SymbolicInputHeap symInputHeap;
        if (prevHeapCG == null) {

            pcHeap = new PathCondition();
            symInputHeap = new SymbolicInputHeap();
        } else {
            pcHeap = ((HeapChoiceGenerator) prevHeapCG).getCurrentPCheap();
            symInputHeap = ((HeapChoiceGenerator) prevHeapCG).getCurrentSymInputHeap();
        }

        String name = env.getStringObject(stringRef);
        String refChain = name + "[-1]"; // why is the type used here? should use the name of the field instead

        SymbolicInteger newSymRef = new SymbolicInteger(refChain);

        // create new HeapNode based on above info
        // update associated symbolic input heap

        pcHeap._addDet(Comparator.EQ, newSymRef, new IntegerConstant(-1));
        ((HeapChoiceGenerator) cg).setCurrentPCheap(pcHeap);
        ((HeapChoiceGenerator) cg).setCurrentSymInputHeap(symInputHeap);
        // System.out.println(">>>>>>>>>>>> initial pcHeap: " + pcHeap.toString());
        return MJIEnv.NULL;
    }

    // makes the fields of object referenced by objvRef symbolic
    // moreover it adds this object to the symbolic heap to participate in lazy initialization
    // -- useful for debugging

    @MJI
    public static void makeFieldsSymbolic(MJIEnv env, int objRef, int stringRef, int objvRef) {
        // makes all the fields of obj v symbolic and adds obj v to the symbolic heap to kick off lazy initialization
        if (objvRef == MJIEnv.NULL)
            throw new RuntimeException("## Error: null object");
        // introduce a heap choice generator for the element in the heap
        ThreadInfo ti = env.getVM().getCurrentThread();
        SystemState ss = env.getVM().getSystemState();
        ChoiceGenerator<?> cg;

        if (!ti.isFirstStepInsn()) {
            cg = new HeapChoiceGenerator(1); // new
            ss.setNextChoiceGenerator(cg);
            env.repeatInvocation();
            return; // not used anyways
        }
        // else this is what really returns results

        cg = ss.getChoiceGenerator();
        assert (cg instanceof HeapChoiceGenerator) : "expected HeapChoiceGenerator, got: " + cg;

        // see if there were more inputs added before
        ChoiceGenerator<?> prevHeapCG = cg.getPreviousChoiceGenerator();
        while (!((prevHeapCG == null) || (prevHeapCG instanceof HeapChoiceGenerator))) {
            prevHeapCG = prevHeapCG.getPreviousChoiceGenerator();
        }

        PathCondition pcHeap;
        SymbolicInputHeap symInputHeap;
        if (prevHeapCG == null) {

            pcHeap = new PathCondition();
            symInputHeap = new SymbolicInputHeap();
        } else {
            pcHeap = ((HeapChoiceGenerator) prevHeapCG).getCurrentPCheap();
            symInputHeap = ((HeapChoiceGenerator) prevHeapCG).getCurrentSymInputHeap();
        }

        // set all the fields to be symbolic
        ClassInfo ci = env.getClassInfo(objvRef);
        FieldInfo[] fields = ci.getDeclaredInstanceFields();
        FieldInfo[] staticFields = ci.getDeclaredStaticFields();

        String name = env.getStringObject(stringRef);
        String refChain = name + "[" + objvRef + "]"; // why is the type used here? should use the name of the field
                                                      // instead

        SymbolicInteger newSymRef = new SymbolicInteger(refChain);
        // ElementInfo eiRef = DynamicArea.getHeap().get(objvRef);
        ElementInfo eiRef = VM.getVM().getHeap().getModifiable(objvRef);
        Helper.initializeInstanceFields(fields, eiRef, refChain);
        Helper.initializeStaticFields(staticFields, ci, ti);

        // create new HeapNode based on above info
        // update associated symbolic input heap

        ClassInfo typeClassInfo = eiRef.getClassInfo();

        HeapNode n = new HeapNode(objvRef, typeClassInfo, newSymRef);
        symInputHeap._add(n);
        pcHeap._addDet(Comparator.NE, newSymRef, new IntegerConstant(-1));
        ((HeapChoiceGenerator) cg).setCurrentPCheap(pcHeap);
        ((HeapChoiceGenerator) cg).setCurrentSymInputHeap(symInputHeap);
        // System.out.println(">>>>>>>>>>>> initial pcHeap: " + pcHeap.toString());
        return;
    }

    private static String res;

    /**
     * assumes the heap with root n is a tree should be generalized to graphs - DONE. not general - do not use this.
     *
     */
    static void buildHeapTree(MJIEnv env, int n) {
        res += " { ";
        res += ((n == MJIEnv.NULL) ? " -1 " : " 0 ");
        if (n != MJIEnv.NULL) {
            ClassInfo ci = env.getClassInfo(n);
            FieldInfo[] fields = ci.getDeclaredInstanceFields();
            for (int i = 0; i < fields.length; i++)
                if (fields[i] instanceof ReferenceFieldInfo) {
                    String fname = fields[i].getName();
                    System.out.println("field name " + fname);
                    buildHeapTree(env, env.getReferenceField(n, fname));
                }
        }
        res = res + " } ";

    }

    @MJI
    public static void printHeapPC(MJIEnv env, int objRef, int msgRef) {
        // should first solve the pc's!!!!

        VM vm = env.getVM();
        ChoiceGenerator<?> cg = vm.getChoiceGenerator();
        PathCondition pc = null;

        if (!(cg instanceof HeapChoiceGenerator)) {
            ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
            while (!((prev_cg == null) || (prev_cg instanceof HeapChoiceGenerator))) {
                prev_cg = prev_cg.getPreviousChoiceGenerator();
            }
            cg = prev_cg;
        }

        if ((cg instanceof HeapChoiceGenerator) && cg != null)
            pc = ((HeapChoiceGenerator) cg).getCurrentPCheap();

        if (pc != null)
            System.out.println(env.getStringObject(msgRef) + pc);
        else
            System.out.println(env.getStringObject(msgRef) + "HeapPC is null");
    }

    // the heap shape is captured in the sequence
    private static String sequence;
    // set to keep track of objects already visited; avoids revisiting
    private static HashSet<Integer> discovered;

    private static HashSet<ClassInfo> discoveredClasses; // to keep track of static fields

    // goes through heap rooted in objvRef in DFS order and prints the symbolic heap
    // does not print the static fields
    @MJI
    public static void printSymbolicRef(MJIEnv env, int objRef, int objvRef, int msgRef) {
        discovered = new HashSet<Integer>();
        discoveredClasses = new HashSet<ClassInfo>();
        sequence = "";

        System.out.println("Rooted Heap: \n" + env.getStringObject(msgRef) + toStringSymbolicRef(env, objvRef) + "\n");
    }

    static String toStringSymbolicRef(MJIEnv env, int objvRef) {
        if (objvRef == MJIEnv.NULL) {
            sequence += "[";
            sequence += "null";
            sequence += "]";

        } else {
            ClassInfo ci = env.getClassInfo(objvRef);
            // ElementInfo ei = DynamicArea.getHeap().get(objvRef);
            ElementInfo ei = VM.getVM().getHeap().get(objvRef);
            sequence += "[" + objvRef + "]";
            if (!discovered.contains(new Integer(objvRef))) {
                discovered.add(new Integer(objvRef));
                sequence += "{";

                FieldInfo[] fields = ci.getDeclaredInstanceFields();

                for (int i = 0; i < fields.length; i++) {
                    FieldInfo fi = fields[i];
                    String fname = fi.getName();
                    Object attr = ei.getFieldAttr(fi);

                    if (fi instanceof ReferenceFieldInfo) {
                        // System.out.println("field name " + fname);

                        sequence += fname + ":";
                        int ref = env.getReferenceField(objvRef, fname);
                        // check if field is symbolic

                        if (attr != null) // we reached a symbolic heap node
                            sequence += "*";
                        else
                            toStringSymbolicRef(env, ref);
                    } else {

                        // System.out.println("field name " + fname);

                        if (attr != null) // we reached a symbolic primitive field
                            sequence += fname + ":" + (Expression) attr + " ";
                        else {
                            sequence += fname + ":" + fi.valueToString(ei.getFields()) + " ";
                            // etc: use FieldInfo.valueToString(fields)
                        }
                    }

                }
                sequence += "}";
            }

            FieldInfo[] staticFields = ci.getDeclaredStaticFields();
            if (staticFields != null && staticFields.length > 0) {

                if (!discoveredClasses.contains(ci)) {
                    sequence += "\n STATICS:";
                    discoveredClasses.add(ci);
                    sequence += "{";

                    for (int i = 0; i < staticFields.length; i++) {
                        FieldInfo fi = staticFields[i];
                        String fname = fi.getName();

                        StaticElementInfo sei = ci.getStaticElementInfo();
                        if (sei == null) {
                            ci.registerClass(env.getVM().getCurrentThread());
                        }
                        Object attr = sei.getFieldAttr(staticFields[i]);

                        if (staticFields[i] instanceof ReferenceFieldInfo) {

                            // System.out.println("field name " + fname);
                            sequence += fname + ":";
                            int refStatic = env.getStaticReferenceField(ci.getName(), fname);

                            if (attr != null) // we reached a symbolic heap node
                                sequence += "*";
                            else
                                toStringSymbolicRef(env, refStatic);
                        }

                        else {
                            if (attr != null) // we reached a symbolic primitive node
                                sequence += fname + ":" + (Expression) attr + " ";
                            else
                                sequence += fname + ":" + fi.valueToString(sei.getFields()) + " ";
                        }

                    }
                    sequence += "}";
                }
            }
        }
        return sequence;
    }

    /**
     * @author Mithun Acharya
     */

    /**
     * Assumes rooted heap. A rooted heap is a pair <r, h> of a root object r and a heap h such that all objects in h
     * are reachable from r
     *
     * Performs a DFS over objects reachable from the root, recursively.
     *
     * Note: In DFS, discovery and finish time of nodes have parenthesis structure.
     *
     *
     */
    private static String traverseRootedHeapAndGetSequence(MJIEnv env, int n) {
        // lets call the current vertex v
        if (n == MJIEnv.NULL) { // vertex v is null
            // for null vertex, discovery and finish time are the same
            // so open and close the bracket all in one place.
            sequence += "{";
            sequence += "-1";
            sequence += "}";
        } else { // vertex v, is not null
            if (!discovered.contains(new Integer(n))) { // vertex v just discovered
                // discovery time for v - so put v into the hashset and open paranthesis
                discovered.add(new Integer(n));
                sequence += "{";
                sequence += "0";

                // Now start traversing all undiscovered successors of v
                ClassInfo ci = env.getClassInfo(n);
                FieldInfo[] fields = ci.getDeclaredInstanceFields();
                for (int i = 0; i < fields.length; i++)
                    if (fields[i] instanceof ReferenceFieldInfo) {
                        String fname = fields[i].getName();
                        // System.out.println("field name " + fname);
                        int temp = env.getReferenceField(n, fname);
                        // null (short-circuited) OR successor yet undiscovered
                        if (temp == MJIEnv.NULL || !discovered.contains(new Integer(temp))) {
                            traverseRootedHeapAndGetSequence(env, temp);
                        }
                    }
                // All undiscovered successors of v are discovered. We are finished with v.
                // finish time for v - so, close parenthesis.
                sequence += "}";
            } else { // vertex v is already discovered - do nothing
            }
        }
        return sequence;
    }

    /**
     *
     * Linearizes the heap.
     *
     */
    private static String linearizeRootedHeap(MJIEnv env, int rootRef) {
        // create a new map to store ids of visited objects
        // storing is done to avoid revisiting.
        discovered = new HashSet<Integer>();
        // "empty" the sequence
        sequence = "";
        // get the sequence for this rooted heap.
        sequence = traverseRootedHeapAndGetSequence(env, rootRef);
        return sequence;
    }

    // Abstraction used
    // Should be made configuration option
    private static final int HEAP_SHAPE_ABSTRACTION = 1;
    private static final int FIELD_ABSTRACTION = 2;
    private static final int OBSERVER_ABSTRACTION = 3;
    private static final int BRANCH_ABSTRACTION = 4;
    // by default, the abstraction is based on heap shape.
    private static final int ABSTRACTION = HEAP_SHAPE_ABSTRACTION;

    /**
     * Abstraction based on heap shape
     */
    private static String getHeapShapeAbstractedState(MJIEnv env, int objvRef) {
        // get the sequence for the rooted heap through heap linearization
        String sequence = linearizeRootedHeap(env, objvRef);
        return sequence;
    }

    /**
     * sequence is value of the field or combination of fields. right now, I will include all non-reference fields which
     * are integers. for now, state is represented by the concatenation of all non-reference integer fields
     */
    private static String getFieldAbstractedState(MJIEnv env, int objvRef) {
        String sequence = "";
        ClassInfo ci = env.getClassInfo(objvRef);
        FieldInfo[] fields = ci.getDeclaredInstanceFields();
        for (int i = 0; i < fields.length; i++)
            if (!(fields[i] instanceof ReferenceFieldInfo)) {
                String fname = fields[i].getName();
                // System.out.println("field name " + fname);
                String type = fields[i].getType();
                if (type.equals("int")) {
                    sequence = sequence + env.getIntField(objvRef, fname);
                }
            }
        return sequence;
    }

    /**
     * Abstraction is based on user-provided observer method. Right now, hardcoded implementation wrt isZero() observer
     * method of IncDec.java Hence it works only with IncDecDriverAbstraction.java Find out how to invoke observer
     * method on the object here!
     *
     */
    private static String getObserverAbstractedState(MJIEnv env, int objvRef) {
        ClassInfo ci = env.getClassInfo(objvRef);
        FieldInfo[] fields = ci.getDeclaredInstanceFields();
        String fname = fields[0].getName(); // should be global
        int global = env.getIntField(objvRef, fname);
        if (global == 0)
            return "isZero()==True";
        else
            return "isZero()==False";
    }

    /**
     *
     * currently, not sure what to do
     */
    private static String getBranchAbstractedState(MJIEnv env, int objvRef) {
        return null;
    }

    /**
     * Simply gets the abstracted state (as a String sequence) depending on user-defined abstraction
     */
    private static String getAbstractedState(MJIEnv env, int objvRef) {
        // get the abstracted state as a string sequence based on the abstraction
        String abstractedState = null;
        switch (ABSTRACTION) { // the abstraction for the object state machine.
        case HEAP_SHAPE_ABSTRACTION:
            abstractedState = getHeapShapeAbstractedState(env, objvRef);
            break;
        case FIELD_ABSTRACTION:
            abstractedState = getFieldAbstractedState(env, objvRef);
            break;
        case OBSERVER_ABSTRACTION:
            abstractedState = getObserverAbstractedState(env, objvRef);
            break;
        case BRANCH_ABSTRACTION:
            abstractedState = getBranchAbstractedState(env, objvRef);
            break;
        default:
            break;
        }
        return abstractedState;
    }

    // stores abstract states seen so far
    private static Set<String> abstracStatesSeenSoFar = new HashSet<String>();
    public static final int NEW_STATE = 1;
    public static final int OLD_STATE = 2;

    /**
     * Is the state seen before? Update AND return NEW_STATE if state is new. if state is old, return OLD_STATE
     */
    public static int checkAndUpdateAbstractStatesSeenSoFar(String state) {
        // the contains check is redundant. retained for clarity.
        if (!abstracStatesSeenSoFar.contains(state)) {
            abstracStatesSeenSoFar.add(state);
            return NEW_STATE; // new state
        }
        return OLD_STATE; // state seen before.
    }

    /**
     *
     * Performs abstract matching
     *
     */
    @MJI
    public static boolean matchAbstractState(MJIEnv env, int objRef, int objvRef) {
        // get the sequence for the abstracted state
        String abstractedState = getAbstractedState(env, objvRef);

        if (checkAndUpdateAbstractStatesSeenSoFar(abstractedState) == NEW_STATE) {
            System.out.println("new state");
            return false; // Verify.ignoreIf will not ignore this state.
        }

        System.out.println("old state");
        return true; // Verify.ignoreIf will ignore this state.
    }

    /* YN: user-defined cost*/
    @MJI
    public static void addCost(MJIEnv env, int objRef, int objvRef) {
        ClassInfo ci = env.getClassInfo(objvRef);
        ElementInfo ei = VM.getVM().getHeap().get(objvRef);
        FieldInfo[] fields = ci.getDeclaredInstanceFields();

        Expression symbolicExpression = null;
        int concreteValue = 0;
        
        if (fields.length != 1) {
            throw new RuntimeException("fields.length != 1 (Debug.addCost)");
        }
        
        FieldInfo fi = fields[0];
        Object attr = ei.getFieldAttr(fi);
        int intValue = ei.getIntField(fi);
        concreteValue = intValue;
        
        if (attr != null) { // we reached a symbolic primitive field
            symbolicExpression = (Expression) attr;
        }

        /*
         * So far we only handle positive cost. Reason: AFL uses a u64 for the cost, so we would run into problems by
         * using negative numbers.
         */
    
        if (concreteValue > 0) {
            Observations.lastObservedCost += concreteValue;
        }

        if (symbolicExpression != null) {
            Observations.lastObservedSymbolicExpression = symbolicExpression;
        } 

    }
    
    @MJI
    public static double getLastMeasuredMetricValue(MJIEnv env, int objRef) {
        return Observations.lastMeasuredMetricValue;
    }
    
    @MJI
    public static void setLastObservedInputSize(MJIEnv env, int objRef, int objvRef) {
        ClassInfo ci = env.getClassInfo(objvRef);
        ElementInfo ei = VM.getVM().getHeap().get(objvRef);
        FieldInfo[] fields = ci.getDeclaredInstanceFields();

        int concreteValue = 0;
        
        if (fields.length != 1) {
            throw new RuntimeException("fields.length != 1 (Debug.addCost)");
        }
        
        FieldInfo fi = fields[0];
        int intValue = ei.getIntField(fi);
        concreteValue = intValue;
        
        Observations.lastObservedInputSize = concreteValue;
    }
    
    @MJI
    public static int getLastObservedInputSize(MJIEnv env, int objRef) {
        return Observations.lastObservedInputSize;
    }
    
    @MJI
    public static void clearMeasurements(MJIEnv env, int objRef) {
        Observations.lastMeasuredMetricValue = 0.0;
    }
    
    

}
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

package gov.nasa.jpf.symbc.bytecode;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.symbc.arrays.ArrayExpression;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.MinMax;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.PreCondition;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.vm.AnnotationInfo;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.LocalVarInfo;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.SystemState;
import gov.nasa.jpf.vm.ThreadInfo;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.StringTokenizer;
import java.util.Vector;

public class BytecodeUtils {

    // static boolean symClass = false;
    /*
     * Helper method to determine if the method just executed is one of the ones specified in the symbolic.method
     * property Matched based on method name (short version) & number of params (if any) For methods without arguments,
     * all methods with this name will be treated as symbolic methods since we cannot distinguish between them;
     */
    public static boolean isMethodSymbolic(Config conf, String methodName, int numberOfArgs, Vector<String> args) {
        // System.out.println("method name "+methodName);
        String[] methods = conf.getStringArray("symbolic.method");
        boolean misMatchedArgs = false;
        String shortName = "";
        if (methods != null) {
            List<String> list = Arrays.asList(methods);
            Iterator<String> it = list.iterator();

            shortName = methodName;

            if (methodName.contains("("))
                shortName = methodName.substring(0, methodName.indexOf("("));
            // System.out.println("short method name "+shortName);
            while (it.hasNext()) {
                String m1 = (String) it.next();
                String configMethodName = m1.substring(0, m1.indexOf("("));
                int argNum;
                if (m1.equals(shortName + "()"))
                    argNum = 0;
                else
                    argNum = m1.split("#").length; // number of args

                if (configMethodName.equalsIgnoreCase(shortName)) {
                    // System.out.println("config method name "+configMethodName + " "+argNum + " "+numberOfArgs);
                    if (argNum == numberOfArgs) {
                        if (args != null) {
                            String argString = m1.substring(m1.indexOf("(") + 1, m1.indexOf(")"));
                            StringTokenizer st = new StringTokenizer(argString, "#");
                            while (st.hasMoreTokens())
                                args.add(st.nextToken());
                        }
                        return true;
                    } else
                        misMatchedArgs = true;
                }

            }

        }
        if (misMatchedArgs) {
            throw new RuntimeException(
                    "ERROR: method arguments do not match with JPF's symbolic.method configuration: " + shortName);
        }
        return false;
    }

    /*
     * Uses the class name to determine if a method is symbolic; use to declare all methods in the given class as
     * symbolic
     */

    public static boolean isClassSymbolic(Config conf, String className, MethodInfo mi, String methodName) {
        String shortName = "";
        if (methodName.contains("init") && methodName.contains(">"))
            shortName = methodName.substring(1, methodName.indexOf('>'));
        String[] classes = conf.getStringArray("symbolic.class");
        if (classes != null) {
            List<String> list = Arrays.asList(classes);
            Iterator<String> it = list.iterator();
            while (it.hasNext()) {
                String cName = (String) it.next();
                if (className.equalsIgnoreCase(cName) && !shortName.equalsIgnoreCase("init") && !mi.isClinit()
                        && !methodName.equalsIgnoreCase("[clinit]<clinit>")
                        && !methodName.equalsIgnoreCase("main([Ljava/lang/String;)V")) {
                    System.out.println("method name " + methodName);
                    // symClass = true;
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * A container for BytecodeUtils.execute to return either the next instruction to execute or to tell the calling
     * method to call super.execute();
     *
     *
     */
    public static class InstructionOrSuper {
        private InstructionOrSuper() {
            this.callSuper = false;
            this.inst = null;
        }

        private InstructionOrSuper(boolean callSuper, Instruction inst) {
            this.callSuper = callSuper;
            this.inst = inst;
        }

        /**
         * Ignore the value of 'inst' and just call the instruction's super.execute() method.
         */
        public final boolean callSuper;

        /**
         * The next instruction for the VM to execute if callSuper == false.
         */
        public final Instruction inst;
    }

    /**
     * Execute INVOKESPECIAL, INVOKESTATIC, and INVOKEVIRTUAL symbolically.
     * 
     * @param invInst
     *            The instance of INVOKESPECIAL, INVOKESTATIC, or INVOKEVIRTUAL
     * @param ss
     *            The VM's system state
     * @param ks
     *            The VM's kernel state
     * @param th
     *            The current thread info
     * @return an InstructionOrSuper instance saying what to do next.
     */
    public static InstructionOrSuper execute(JVMInvokeInstruction invInst, ThreadInfo th) {
        boolean isStatic = (invInst instanceof INVOKESTATIC);
        String bytecodeName = invInst.getMnemonic().toUpperCase();
        String mname = invInst.getInvokedMethodName();
        String cname = invInst.getInvokedMethodClassName();

        MethodInfo mi = invInst.getInvokedMethod(th);

        if (mi == null) {
            return new InstructionOrSuper(false,
                    th.createAndThrowException("java.lang.NoSuchMethodException", "calling " + cname + "." + mname));
        }

        /*
         * Here we test if the the method should be executed symbolically. We perform two checks: 1. Does the invoked
         * method correspond to a method listed in the symbolic.method property and does the number of parameters match?
         * 2. Is the method contained in a class that is to be executed symbolically? If the method is symbolic,
         * initialize the parameter attributes and the fields if they are specified as symbolic based on annotations
         *
         */

        String longName = mi.getFullName();
        String[] argTypes = mi.getArgumentTypeNames();
        // System.out.println(longName);

        int argSize = argTypes.length; // does not contain "this"

        Vector<String> args = new Vector<String>();
        Config conf = th.getVM().getConfig();

        // Start string handling: TODO corina it needs reviewing as it does not seem to be correct
        /**** This is where we branch off to handle symbolic string variables *******/
        String[] symstrings = conf.getStringArray("symbolic.strings");
        boolean symstrings_flag = (symstrings != null && symstrings[0].equalsIgnoreCase("true")) ? true : false;
        if (symstrings_flag) {

            SymbolicStringHandler a = new SymbolicStringHandler();
            Instruction handled = a.handleSymbolicStrings(invInst, th);
            if (handled != null) { // go to next instruction as symbolic string operation was done
                // System.out.println("Symbolic string analysis!!!"+invInst);
                return new InstructionOrSuper(false, handled);
            }
        }
        // End string handling

        boolean symClass = BytecodeUtils.isClassSymbolic(conf, cname, mi, mname);
        boolean found = (BytecodeUtils.isMethodSymbolic(conf, longName, argSize, args) || symClass);
        if (found) {
            // method is symbolic

            // create a choice generator to associate the precondition with it
            ChoiceGenerator<?> cg = null;
            if (invInst.getInvokedMethod().getAnnotation("gov.nasa.jpf.symbc.Preconditions") != null
                    || conf.getStringArray("symbolic.arrays") != null) {
                if (!th.isFirstStepInsn()) { // first time around
                    cg = new PCChoiceGenerator(1);
                    th.getVM().setNextChoiceGenerator(cg);
                    return new InstructionOrSuper(false, invInst);
                } else { // this is what really returns results
                    cg = th.getVM().getChoiceGenerator();
                    if (!(cg instanceof PCChoiceGenerator)) // the choice comes from super
                        return new InstructionOrSuper(true, null);
                }
            }

            String outputString = "\n***Execute symbolic " + bytecodeName + ": " + mname + "  (";

            LocalVarInfo[] argsInfo = mi.getArgumentLocalVars();

            int localVarsIdx = 0;
            // if debug option was not used when compiling the class,
            // then we do not have names of the locals

            if (argsInfo != null) {
                localVarsIdx = (isStatic ? 0 : 1); // Skip over "this" argument when non-static
            } else {
                throw new RuntimeException("ERROR: you need to turn debug option on");
            }
            Map<String, Expression> expressionMap = new HashMap<String, Expression>();

            // take care of the method arguments
            StackFrame sf = th.getModifiableTopFrame();// get a hold of the stack frame of the caller

            // number of words; we skip over 'this' for non-static methods
            int numStackSlots = invInst.getArgSize() - (isStatic ? 0 : 1);

            int stackIdx = numStackSlots - 1; // stackIdx ranges from numStackSlots-1 to 0

            // special treatment of "this"
            String lazy[] = conf.getStringArray("symbolic.lazy");
            String symarrays[] = conf.getStringArray("symbolic.arrays");
            boolean symarray = false;
            if (symarrays != null) {
                symarray = symarrays[0].equalsIgnoreCase("true");
            }
            // TODO: to review
            // if(lazy != null) {
            // if(lazy[0].equalsIgnoreCase("true")) {
            // if(!isStatic) {
            //// String name = "this";
            //// IntegerExpression sym_v = new SymbolicInteger(varName(name, VarType.REF));
            //// expressionMap.put(name, sym_v);
            //// sf.setOperandAttr(0, sym_v);
            //// outputString = outputString.concat(" " + sym_v + ",");
            // }
            // }
            // }

            for (int j = 0; j < argSize; j++) { // j ranges over actual arguments
                if (symClass || args.get(j).equalsIgnoreCase("SYM")) {
                    String name = argsInfo[localVarsIdx].getName();
                    if (argTypes[j].equalsIgnoreCase("int")) {
                        IntegerExpression sym_v = new SymbolicInteger(varName(name, VarType.INT));
                        expressionMap.put(name, sym_v);
                        sf.setOperandAttr(stackIdx, sym_v);
                        outputString = outputString.concat(" " + sym_v + ",");
                    } else if (argTypes[j].equalsIgnoreCase("long")) {
                        String varname = varName(name, VarType.INT);
                        IntegerExpression sym_v = new SymbolicInteger(varname, MinMax.getVarMinLong(varname),
                                MinMax.getVarMaxLong(varname));
                        expressionMap.put(name, sym_v);
                        sf.setOperandAttr(stackIdx, sym_v);
                        outputString = outputString.concat(" " + sym_v + ",");
                    } else if (argTypes[j].equalsIgnoreCase("short")) {
                        String varname = varName(name, VarType.INT);
                        IntegerExpression sym_v = new SymbolicInteger(varname, MinMax.getVarMinShort(varname),
                                MinMax.getVarMaxShort(varname));
                        expressionMap.put(name, sym_v);
                        sf.setOperandAttr(stackIdx, sym_v);
                        outputString = outputString.concat(" " + sym_v + ",");
                    } else if (argTypes[j].equalsIgnoreCase("byte")) {
                        String varname = varName(name, VarType.INT);
                        IntegerExpression sym_v = new SymbolicInteger(varname, MinMax.getVarMinByte(varname),
                                MinMax.getVarMaxByte(varname));
                        expressionMap.put(name, sym_v);
                        sf.setOperandAttr(stackIdx, sym_v);
                        outputString = outputString.concat(" " + sym_v + ",");
                    } else if (argTypes[j].equalsIgnoreCase("char")) {
                        String varname = varName(name, VarType.INT);
                        IntegerExpression sym_v = new SymbolicInteger(varname, MinMax.getVarMinChar(varname),
                                MinMax.getVarMaxChar(varname));
                        expressionMap.put(name, sym_v);
                        sf.setOperandAttr(stackIdx, sym_v);
                        outputString = outputString.concat(" " + sym_v + ",");
                    } else if (argTypes[j].equalsIgnoreCase("float") || argTypes[j].equalsIgnoreCase("double")) {
                        String varname = varName(name, VarType.REAL);
                        RealExpression sym_v = new SymbolicReal(varname, MinMax.getVarMinDouble(varname),
                                MinMax.getVarMaxDouble(varname));
                        expressionMap.put(name, sym_v);
                        sf.setOperandAttr(stackIdx, sym_v);
                        outputString = outputString.concat(" " + sym_v + ",");
                    } else if (argTypes[j].equalsIgnoreCase("boolean")) {
                        IntegerExpression sym_v = new SymbolicInteger(varName(name, VarType.INT), 0, 1);
                        // treat boolean as an integer with range [0,1]
                        expressionMap.put(name, sym_v);
                        sf.setOperandAttr(stackIdx, sym_v);
                        outputString = outputString.concat(" " + sym_v + ",");
                    } else if (argTypes[j].equalsIgnoreCase("java.lang.String")) {
                        StringExpression sym_v = new StringSymbolic(varName(name, VarType.STRING));
                        expressionMap.put(name, sym_v);
                        sf.setOperandAttr(stackIdx, sym_v);
                        outputString = outputString.concat(" " + sym_v + ",");
                    } else if (argTypes[j].equalsIgnoreCase("int[]") || argTypes[j].equalsIgnoreCase("long[]")
                            || argTypes[j].equalsIgnoreCase("byte[]")) {
                        if (symarray) {
                            ArrayExpression sym_v = new ArrayExpression(th.getElementInfo(sf.peek()).toString());
                            expressionMap.put(name, sym_v);
                            sf.setOperandAttr(stackIdx, sym_v);
                            outputString = outputString.concat(" " + sym_v + ",");

                            PCChoiceGenerator prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
                            PathCondition pc;
                            if (prev_cg == null)
                                pc = new PathCondition();
                            else
                                pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();

                            pc._addDet(Comparator.GE, sym_v.length, new IntegerConstant(0));
                            ((PCChoiceGenerator) cg).setCurrentPC(pc);
                        } else {
                            Object[] argValues = invInst.getArgumentValues(th);
                            ElementInfo eiArray = (ElementInfo) argValues[j];

                            if (eiArray != null)
                                for (int i = 0; i < eiArray.arrayLength(); i++) {
                                    IntegerExpression sym_v = new SymbolicInteger(varName(name + i, VarType.INT));
                                    expressionMap.put(name + i, sym_v);
                                    eiArray.addElementAttr(i, sym_v);
                                    outputString = outputString.concat(" " + sym_v + ",");
                                }
                            else
                                System.out.println("Warning: input array empty! " + name);
                        }
                    } else if (argTypes[j].equalsIgnoreCase("float[]") || argTypes[j].equalsIgnoreCase("double[]")) {
                        if (symarray) {
                            ArrayExpression sym_v = new ArrayExpression(th.getElementInfo(sf.peek()).toString());
                            expressionMap.put(name, sym_v);
                            sf.setOperandAttr(stackIdx, sym_v);
                            outputString = outputString.concat(" " + sym_v + ",");

                            PCChoiceGenerator prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
                            PathCondition pc;
                            if (prev_cg == null)
                                pc = new PathCondition();
                            else
                                pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();

                            pc._addDet(Comparator.GE, sym_v.length, new IntegerConstant(0));
                            ((PCChoiceGenerator) cg).setCurrentPC(pc);
                        } else {
                            Object[] argValues = invInst.getArgumentValues(th);
                            ElementInfo eiArray = (ElementInfo) argValues[j];

                            if (eiArray != null)
                                for (int i = 0; i < eiArray.arrayLength(); i++) {
                                    RealExpression sym_v = new SymbolicReal(varName(name + i, VarType.REAL));
                                    expressionMap.put(name + i, sym_v);
                                    eiArray.addElementAttr(i, sym_v);
                                    outputString = outputString.concat(" " + sym_v + ",");
                                }
                            else
                                System.out.println("Warning: input array empty! " + name);
                        }
                    } else if (argTypes[j].equalsIgnoreCase("boolean[]")) {
                        if (symarray) {
                            ArrayExpression sym_v = new ArrayExpression(th.getElementInfo(sf.peek()).toString());
                            expressionMap.put(name, sym_v);
                            sf.setOperandAttr(stackIdx, sym_v);
                            outputString = outputString.concat(" " + sym_v + ",");

                            PCChoiceGenerator prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
                            PathCondition pc;
                            if (prev_cg == null)
                                pc = new PathCondition();
                            else
                                pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();

                            pc._addDet(Comparator.GE, sym_v.length, new IntegerConstant(0));
                            ((PCChoiceGenerator) cg).setCurrentPC(pc);
                        } else {
                            Object[] argValues = invInst.getArgumentValues(th);
                            ElementInfo eiArray = (ElementInfo) argValues[j];

                            if (eiArray != null)
                                for (int i = 0; i < eiArray.arrayLength(); i++) {
                                    IntegerExpression sym_v = new SymbolicInteger(varName(name + i, VarType.INT), 0, 1);
                                    expressionMap.put(name + i, sym_v);
                                    eiArray.addElementAttr(i, sym_v);
                                    outputString = outputString.concat(" " + sym_v + ",");
                                }
                            else
                                System.out.println("Warning: input array empty! " + name);
                        }
                    } else if (argTypes[j].contains("[]")) {
                        if (symarray) {
                            Object[] argValues = invInst.getArgumentValues(th);
                            ElementInfo eiArray = (ElementInfo) argValues[j];
                            // If the type name contains [] but wasn't catched previously, it is an object array
                            ArrayExpression sym_v = new ArrayExpression(th.getElementInfo(sf.peek()).toString(),
                                    argTypes[j].substring(0, argTypes[j].length() - 2));
                            // We remove the [] at the end of the type to keep only the type of the object
                            expressionMap.put(name, sym_v);
                            sf.setOperandAttr(stackIdx, sym_v);
                            outputString = outputString.concat(" " + sym_v + ",");

                            PCChoiceGenerator prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
                            PathCondition pc;
                            if (prev_cg == null)
                                pc = new PathCondition();
                            else
                                pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();

                            pc._addDet(Comparator.GE, sym_v.length, new IntegerConstant(0));
                            ((PCChoiceGenerator) cg).setCurrentPC(pc);
                        }

                    } else {
                        // the argument is of reference type and it is symbolic
                        if (lazy != null) {
                            if (lazy[0].equalsIgnoreCase("true")) {
                                IntegerExpression sym_v = new SymbolicInteger(varName(name, VarType.REF));
                                expressionMap.put(name, sym_v);
                                sf.setOperandAttr(stackIdx, sym_v);
                                outputString = outputString.concat(" " + sym_v + ",");
                            }
                        }
                        // throw new RuntimeException("## Error: parameter type not yet handled: " + argTypes[j]);
                    }

                } else
                    outputString = outputString.concat(" " + argsInfo[localVarsIdx].getName() + "_CONCRETE" + ",");

                if (argTypes[j].equalsIgnoreCase("long") || argTypes[j].equalsIgnoreCase("double")) {
                    stackIdx--;
                }
                stackIdx--;
                localVarsIdx++;
            }

            if (outputString.endsWith(","))
                outputString = outputString.substring(0, outputString.length() - 1);
            outputString = outputString + " )  (";

            // now, take care of any globals that are indicated as symbolic
            // base on annotation or on symbolic.fields property
            // annotation will override the symbolic.fields property as a
            // way to specify exceptions
            String[] symFields = conf.getStringArray("symbolic.fields");
            boolean symStatic = false;
            boolean symInstance = false;
            if (symFields != null) {
                List<String> symList = Arrays.asList(symFields);
                for (int i = 0; i < symList.size(); i++) {
                    String s = (String) symList.get(i);
                    if (s.equalsIgnoreCase("instance"))
                        symInstance = true;
                    else if (s.equalsIgnoreCase("static"))
                        symStatic = true;
                }
            }
            int index = 1;
            ClassInfo ci = mi.getClassInfo();
            FieldInfo[] fields = ci.getDeclaredInstanceFields();
            ElementInfo ei;
            if (isStatic) {
                ei = th.getElementInfo(ci.getClassObjectRef());
            } else {
                int objRef = th.getCalleeThis(invInst.getArgSize());
                if (objRef == -1) { // NPE
                    return new InstructionOrSuper(false, th.createAndThrowException("java.lang.NullPointerException",
                            "calling '" + mname + "' on null object"));
                }
                ei = th.getElementInfo(objRef);
            }

            if (fields.length > 0) {
                for (int i = 0; i < fields.length; i++) {
                    String value = "";
                    int objRef = th.getCalleeThis(invInst.getArgSize());
                    if (fields[i].getAnnotation("gov.nasa.jpf.symbc.Symbolic") != null)
                        value = fields[i].getAnnotation("gov.nasa.jpf.symbc.Symbolic").valueAsString();

                    else {
                        if (true == symInstance)
                            value = "true";
                        else
                            value = "false";
                    }
                    if (value.equalsIgnoreCase("true")) {
                        Expression sym_v = Helper.initializeInstanceField(fields[i], ei, "input[" + objRef + "]", "");
                        String name = fields[i].getName();
                        expressionMap.put(name, sym_v);
                        outputString = outputString.concat(" " + name + ",");
                        // outputString = outputString.concat(" " + fullName + ",");
                        index++;
                    }
                }
            }

            FieldInfo[] staticFields = ci.getDeclaredStaticFields();
            if (staticFields.length > 0) {
                for (int i = 0; i < staticFields.length; i++) {
                    String value = "";
                    if (staticFields[i].getAnnotation("gov.nasa.jpf.symbc.Symbolic") != null)
                        value = staticFields[i].getAnnotation("gov.nasa.jpf.symbc.Symbolic").valueAsString();
                    else {
                        if (true == symStatic)
                            value = "true";
                        else
                            value = "false";
                    }
                    if (value.equalsIgnoreCase("true")) {
                        Expression sym_v = Helper.initializeStaticField(staticFields[i], ci, th, "");
                        String name = staticFields[i].getName();
                        expressionMap.put(name, sym_v);
                        outputString = outputString.concat(" " + name + ",");
                        // outputString = outputString.concat(" " + fullName + ",");
                        index++;
                    }
                }
            }

            if (outputString.endsWith(",")) {
                outputString = outputString.substring(0, outputString.length() - 1);
                outputString = outputString + " )";
            } else {
                if (outputString.endsWith("("))
                    outputString = outputString.substring(0, outputString.length() - 1);
            }
            // System.out.println(outputString);

            // Now, set up the initial path condition for this method if the
            // Annotation contains one
            // we'll create a choice generator for this

            // this is pretty inefficient especially when preconditions are not used -- fixed somehow -- TODO: testing

            if (invInst.getInvokedMethod().getAnnotation("gov.nasa.jpf.symbc.Preconditions") != null) {
                AnnotationInfo ai;
                PathCondition pc = null;
                // TODO: should still look at prev pc if we want to generate test sequences
                // here we should get the prev pc
                assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
                ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
                while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
                    prev_cg = prev_cg.getPreviousChoiceGenerator();
                }

                if (prev_cg == null)
                    pc = new PathCondition();
                else
                    pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();

                assert pc != null;

                ai = invInst.getInvokedMethod().getAnnotation("gov.nasa.jpf.symbc.Preconditions");
                String assumeString = (String) ai.getValue("value");

                pc = (new PreCondition()).addConstraints(pc, assumeString, expressionMap);

                // should check PC for satisfiability
                if (!pc.simplify()) {// not satisfiable
                    // System.out.println("Precondition not satisfiable");
                    th.getVM().getSystemState().setIgnored(true);
                } else {
                    // pc.solve();
                    ((PCChoiceGenerator) cg).setCurrentPC(pc);
                    // System.out.println(((PCChoiceGenerator) cg).getCurrentPC());
                }
            }
        }
        return new InstructionOrSuper(true, null);
    }

    /**
     * Get the path condition of a SystemState's most recent PCChoiceGenerator.
     */
    public static PathCondition getPC(SystemState ss) {
        ChoiceGenerator<?> cg = ss.getChoiceGenerator();
        while (cg != null && !(cg instanceof PCChoiceGenerator)) {
            cg = cg.getPreviousChoiceGenerator();
        }

        if (cg == null) {
            return null;
        } else {
            return ((PCChoiceGenerator) cg).getCurrentPC();
        }
    }

    private static int symVarCounter = 1;

    public static void clearSymVarCounter() {
        symVarCounter = 1;
    }

    public enum VarType {
        INT, REAL, REF, STRING
    };

    public static String varName(String name, VarType type) {
        String suffix = "";
        switch (type) {
        case INT:
            suffix = "_SYMINT";
            break;
        case REAL:
            suffix = "_SYMREAL";
            break;
        case REF:
            suffix = "_SYMREF";
            break;
        case STRING:
            suffix = "_SYMSTRING";
            break;
        default:
            throw new RuntimeException("Unhandled SymVarType: " + type);
        }
        return name + "_" + (symVarCounter++) + suffix;
    }

}

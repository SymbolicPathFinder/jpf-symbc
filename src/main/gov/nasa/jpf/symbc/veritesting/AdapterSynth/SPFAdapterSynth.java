package gov.nasa.jpf.symbc.veritesting.AdapterSynth;

import choco.util.Arithm;
import gov.nasa.jpf.jvm.JVMDirectCallStackFrame;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Map;

public class SPFAdapterSynth {
    public static void runAdapterSynth(ThreadInfo ti, StackFrame curr) {
        Map<String, Object> map = null;
//        while (!JVMDirectCallStackFrame.class.isInstance(curr)) {
            /*if (curr.getMethodInfo().getName().equals("concretizeAdapter")) {
                PathCondition pc;
                if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
                    pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
                } else return;
                map = pc.solveWithValuation(null, null);
                ArgSubAdapter argSubAdapter = ArgSubAdapter.randomAdapter();
                for (int i = 0; i < 6; i++) {
                    argSubAdapter.i_is_const[i] = (getVal(map, "i_is_const" + i) != 0);
                    argSubAdapter.i_val[i] = Math.toIntExact(getVal(map, "i_val" + i));
                    argSubAdapter.b_is_const[i] = ((getVal(map, "b_is_const" + i)) != 0);
                    argSubAdapter.b_val[i] = Math.toIntExact(getVal(map,"b_val" + i));
                    argSubAdapter.c_is_const[i] = ((getVal(map, "c_is_const" + i)) != 0);
                    argSubAdapter.c_val[i] = Math.toIntExact(getVal(map, "c_val" + i));
                }
                FileOutputStream file = null;
                ObjectOutputStream out = null;
                try {
                    file = new FileOutputStream("adapter");
                    out = new ObjectOutputStream(file);
//                    out.writeChar('C');
                    ArgSubAdapter.writeAdapter(out, argSubAdapter);
                    out.close();
                    file.close();
                } catch (FileNotFoundException e) {
                    e.printStackTrace();
                } catch (IOException e) {
                    e.printStackTrace();
                }
                System.out.println("concretizeAdapter wrote adapter: " + argSubAdapter);
            } else if (curr.getMethodInfo().getName().equals("abortExecutionPath")) {
                ti.getVM().getSystemState().setIgnored(true);
            } else if (curr.getMethodInfo().getName().equals("concretizeCounterExample")) {
                PathCondition pc;
                if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
                    pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
                } else return;
                map = pc.solveWithValuation(null, null);
                TestInput newInput = new TestInput();
                for (int i = 0; i < 6; i++) {
                    if (map.containsKey("i" + i)) {
                        try {
                            newInput.in[i] = Math.toIntExact(((Long) map.get("i" + i)));
                        } catch(ArithmeticException e) {
                            if (map.get("i" + i).equals(2147483648L)) {
                                newInput.in[i] = -2147483648;
                            } else throw new IllegalArgumentException("Cannot construct value for counterexample input: i" + i);
                        }
                    }
                    else newInput.in[i] = 0;
                    if (map.containsKey("b" + i))
                        newInput.b[i] = (((Long) map.get("b" + i)) != 0);
                    else newInput.b[i] = true;
                    if (map.containsKey("c" + i))
                        newInput.c[i] = (char)Math.toIntExact(((Long) map.get("c" + i)));
                    else newInput.c[i] = 0;
                }
                ArrayList<TestInput> tests = new ArrayList<>();
                try {
                    GetInputsFromFile getInputsFromFile = new GetInputsFromFile("tests", true).invoke();
                    tests = getInputsFromFile.getTestInputs();
                    System.out.println("Read " + tests.size() + " previous tests");
                } catch (IOException | ClassNotFoundException e) {
                    System.out.println("Read no previous tests");
                }
                tests.add(newInput);
                FileOutputStream file;
                ObjectOutputStream out;
                try {
                    file = new FileOutputStream("tests", false);
                    out = new ObjectOutputStream(file);
//                    out.writeChar('A');
                    for (TestInput input: tests) {
                        System.out.println("wrote test: " + input);
                        TestInput.writeTestInput(out, input);
                    }
                    out.close();
                    file.close();
                } catch (FileNotFoundException e) {
                    e.printStackTrace();
                } catch (IOException e) {
                    e.printStackTrace();
                }
                System.out.println("concretizeCounterExample wrote counterExample: " + newInput);
            }*/
//            curr = curr.getPrevious();
//        }
    }

    public static Long getVal(Map<String, Object> map, String s) {
        if (map != null && map.containsKey(s))
            return (Long)map.get(s);
        else return null;
    }
}

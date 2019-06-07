package gov.nasa.jpf.symbc.veritesting.AdapterSynth;

import java.io.EOFException;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.ArrayList;

public class GetInputsFromFile {
    private String arg;
    private ArrayList<TestInput> testInputs = null;
    private ArgSubAdapter adapter = null;
    private FileInputStream fileInputStream;
    private Character c;
    private boolean isFinalAdapter = false;
    private boolean isAdapterSearch;

    public GetInputsFromFile(String arg, boolean isAdapterSearch) {
        this.arg = arg;
        this.isAdapterSearch = isAdapterSearch;
    }

    public ArrayList<TestInput> getTestInputs() {
        return testInputs;
    }

    public Character getC() {
        return c;
    }

    public ArgSubAdapter getAdapter() { return adapter; }

    public GetInputsFromFile invoke() throws IOException, ClassNotFoundException {
            /*
            Assume that the file has the format
            A
            Serialized ArgSubAdapter object
            OR
            C
            Serialized TestInput object 1
            Serialized TestInput object 2
            ...
             */
        fileInputStream = new FileInputStream(arg);
        ObjectInputStream in = new ObjectInputStream(fileInputStream);
//        c = in.readChar();
        if(isAdapterSearch) {
            TestInput testInput = TestInput.readTestInput(in);
            testInputs = new ArrayList<>();
            testInputs.add(testInput);
            while (testInput != null) {
                try {
                    testInput = TestInput.readTestInput(in);
                    testInputs.add(testInput);
                } catch (EOFException e) {
                    testInput = null;
                }
            }
            adapter = null;
        } else {
                adapter = ArgSubAdapter.readAdapter(in);
                // Nothing should exist in the input file after the adapter
                try {
                    in.readObject();
                    assert false;
                } catch(EOFException e) { }
                testInputs = null;
        }

        in.close();
//            fileInputStream.close();
        return this;
    }
}
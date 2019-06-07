package veritesting;

import gov.nasa.jpf.symbc.veritesting.AdapterSynth.TestInput;

public abstract class TestRegionBaseClass {
    // Classes that wish to test a veritesting region should put the region inside a method and call it from a
    // overridden testFunction
    abstract Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                                  boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5,
                                  char c0, char c1, char c2, char c3, char c4, char c5);

    Outputs testFunction(TestInput input) {
        return testFunction(input.in[0], input.in[1], input.in[2], input.in[3], input.in[4], input.in[5],
            input.b[0], input.b[1], input.b[2], input.b[3], input.b[4], input.b[5],
            input.c[0], input.c[1], input.c[2], input.c[3], input.c[4], input.c[5]);}
}
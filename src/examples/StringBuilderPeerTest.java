package tests;

import org.sosy_lab.sv_benchmarks.Verifier;

public class StringBuilderPeerTest {

    public static void main(String[] args) {

        String s = Verifier.nondetString();

        StringBuilder sb = new StringBuilder(s);

        assert sb.length() >= 0;

        int cap = sb.capacity();

        assert cap >= 16;
    }
}
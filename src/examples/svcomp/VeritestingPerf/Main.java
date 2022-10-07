package svcomp.VeritestingPerf;

public class Main {
    public static void main(String[] args) {
/*
        int[] a = new int[2];

        int a0 = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
        int a1 = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();

        a[0] = a0;
        a[1] = a1;

        int i = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();

        if (a0 > 0 && a1 > 0 && i > 0 && i < 2)
            if (a[i] == 0)
                assert false;*/


        int i = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
        int j = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();


        assert(i+j >= 0);

      return;
    }
}


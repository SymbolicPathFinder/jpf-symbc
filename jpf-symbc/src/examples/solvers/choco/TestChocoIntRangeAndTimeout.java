package solvers.choco;

import org.sosy_lab.sv_benchmarks.Verifier;

public class TestChocoIntRangeAndTimeout {
    public static void main(String[] args) {
        int x = Verifier.nondetInt();
        test(x);
    }

    public static void test(int x) {
        int z = x + x;
        if(x < z) {
            assert false;
            System.out.println("Branch F001");
        } else {
            System.out.println("Branch F002");
        }
    }
}

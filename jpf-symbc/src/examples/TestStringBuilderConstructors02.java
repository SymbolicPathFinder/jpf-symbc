import gov.nasa.jpf.symbc.Debug;
import org.sosy_lab.sv_benchmarks.Verifier;

public class TestStringBuilderConstructors02 {

    public static void test() {
        String arg = Verifier.nondetString();
        StringBuilder buffer3 = new StringBuilder(arg);

        assert buffer3.equals(arg);
    }

    public static void main(String[] args) {
        test();
    }
}
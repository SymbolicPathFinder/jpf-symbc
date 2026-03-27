import org.sosy_lab.sv_benchmarks.Verifier;

public class TestStringValueOf07 {

  public static void check(long x) {
    String s = String.valueOf(x);

    if (x == 100000000000L) {
      assert false;
    }
  }

  public static void main(String[] args) {
    long x = Verifier.nondetLong();
    check(x);
  }
}
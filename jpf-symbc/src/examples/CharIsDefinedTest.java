import org.sosy_lab.sv_benchmarks.Verifier;

public class CharIsDefinedTest {
  public static void main(String[] args) {
    // make a symbolic character directly (no string DP required)
    char c = Verifier.nondetChar();

    // we want to exercise Character.isDefined with a symbolic char
    // the symbc peer should cause both outcomes to be explored
    assert Character.isDefined(c) == false;
  }
}

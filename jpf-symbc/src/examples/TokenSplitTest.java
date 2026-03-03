/*
 * Tiny example to exercise String.split handling under symbolic execution.
 * Keeps the same pattern as the existing examples so it can be run via JPF.
 */
import org.sosy_lab.sv_benchmarks.Verifier;

public class TokenSplitTest {
  public static void main(String[] args) {
    String sentence = Verifier.nondetString();
    String[] tokens = sentence.split(" ");

    int i = 0;
    for (String token : tokens) {
      if (i == 3) assert token.equals("genneration");
      ++i;
    }
  }
}

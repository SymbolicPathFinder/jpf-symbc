import org.sosy_lab.sv_benchmarks.Verifier;

public class FloatParserFloatPeerTest {

  public static void main(String[] args) {

    String s = Verifier.nondetString();

    float f = Float.parseFloat(s);

    assert true;
  }
}
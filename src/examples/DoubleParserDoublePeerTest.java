import org.sosy_lab.sv_benchmarks.Verifier;

public class DoubleParserDoublePeerTest {

  public static void main(String[] args) {

    String s = Verifier.nondetString();

    double d = Double.parseDouble(s);

    assert true;
  }
}
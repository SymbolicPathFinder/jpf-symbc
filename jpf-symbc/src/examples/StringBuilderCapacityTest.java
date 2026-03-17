/*
 * Simple example to test symbolic handling of StringBuilder.capacity()
 */
import org.sosy_lab.sv_benchmarks.Verifier;

public class StringBuilderCapacityTest {
  public static void main(String[] args) {
    StringBuilder buffer = new StringBuilder(Verifier.nondetString());
    // this assertion forces JPF to explore capacity-related constraints
    assert buffer.capacity() == 69;
  }
}

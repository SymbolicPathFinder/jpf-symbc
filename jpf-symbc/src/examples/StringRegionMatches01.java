import org.sosy_lab.sv_benchmarks.Verifier;

public class StringRegionMatches01 {
  public static void main(String[] args) {
    String s1 = Verifier.nondetString();
    String s2 = "Hello World";

    // Testing a symbolic string against a concrete string
    if (s1 != null && s1.length() >= 5) {
        if (s1.regionMatches(0, s2, 0, 5)) {
            // Path 1: s1 starts with "Hello"
            assert s1.startsWith("Hello"); 
        } else {
            // Path 2: s1 does not start with "Hello"
            // This is where your previous run found the AssertionError
        }
    }
  }
}

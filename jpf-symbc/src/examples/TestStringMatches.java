import org.sosy_lab.sv_benchmarks.Verifier;

public class TestStringMatches {
    public static void main(String[] args) {
        String sym = Verifier.nondetString();
        
        // Pattern: exactly 3 digits
        if (sym.matches("\\d{3}")) {
            System.out.println("Path 1: String matches 3 digits");
            // Check if length is correctly inferred by the solver
            if (sym.length() != 3) {
                assert false; // This should NOT be reachable
            }
        } else {
            System.out.println("Path 2: String does not match 3 digits");
        }
    }
}

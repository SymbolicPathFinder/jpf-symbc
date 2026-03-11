/*
 * Test for nonlinear floating-point operations with Z3BitVector solver
 * This demonstrates the newly added support for Math functions
 */
public class TestNonlinearZ3 {
    
    public static void main(String[] args) {
        (new TestNonlinearZ3()).test(0.0, 0.0);
    }

    public void test(double x, double y) {
        // Test trigonometric functions
        if (Math.sin(x) > 0.5) {
            System.out.println("Path 1: sin(x) > 0.5");
        }
        
        if (Math.cos(y) < -0.5) {
            System.out.println("Path 2: cos(y) < -0.5");
        }
        
        // Test exponential and logarithm
        if (Math.exp(x) > 2.0) {
            System.out.println("Path 3: exp(x) > 2.0");
        }
        
        // Note: log requires y > 0 to avoid NaN
        // Without explicit domain constraints, uninterpreted functions may find infeasible paths
        if (y > 0.0 && Math.log(y) < 1.0) {
            System.out.println("Path 4: log(y) < 1.0");
        }
        
        // Note: sqrt requires x >= 0 to avoid NaN
        // Without explicit domain constraints, uninterpreted functions may find infeasible paths
        if (x >= 0.0 && Math.sqrt(x) > 1.5) {
            System.out.println("Path 5: sqrt(x) > 1.5");
        }
        
        // Test power
        if (Math.pow(x, 2.0) > 4.0) {
            System.out.println("Path 6: pow(x, 2.0) > 4.0");
        }
        
        // Test arctangent
        if (Math.atan(x) > 0.7) {
            System.out.println("Path 7: atan(x) > 0.7");
        }
        
        // Test atan2
        if (Math.atan2(x, y) > 0.0) {
            System.out.println("Path 8: atan2(x, y) > 0.0");
        }
        
        System.out.println("Test completed successfully");
    }
}


package jpf.symbc;

import org.junit.Test;
import static org.junit.Assert.*;

public class AppTest {
    @Test 
    public void testAppHasAGreeting() {
        App classUnderTest = new App();
        assertNotNull("app should have a greeting", classUnderTest.getGreeting());
    }
}

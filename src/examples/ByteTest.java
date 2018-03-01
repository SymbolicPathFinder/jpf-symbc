import gov.nasa.jpf.symbc.Debug;

/**
 * @author corina pasareanu corina.pasareanu@sv.cmu.edu
 *
 */

public class ByteTest {
	public static void test(byte b1, byte b2) {
		if (b1==b2)
			System.out.println("br 1");
		else
			System.out.println("br 2");
	}
	
	// The test driver
	public static void main(String[] args) {
		byte b1=(byte)Debug.makeSymbolicInteger("b1");
		byte b2=(byte)Debug.makeSymbolicInteger("b2");
		test(b1,b2);
		System.out.println("PC "+Debug.getPC_prefix_notation());
	}
}

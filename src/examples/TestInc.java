import gov.nasa.jpf.symbc.Debug;

/**
 * @author corina pasareanu corina.pasareanu@sv.cmu.edu
 *
 */

public class TestInc {

	  public static void main(String args[]) {
	    try {
	      double d1 = Debug.makeSymbolicReal("d1");//Verifier.nondetDouble();
	      double d2 = Debug.makeSymbolicReal("d2");//Verifier.nondetDouble();

	      // layer 0
	      double res0 = 1.0*d1+1.0*d2+1.0;
	      if(res0>0) // YN: changed d1 to res
	          System.out.println("gt0");
	      else
	          System.out.println("le0");
	      
	      // layer 1
	    double res1 = 1.0*d1-1.0*d2+1.0;
	    if(res1>0)
	        System.out.println("gt1");
	    else
	        System.out.println("le1");
	      
	    } catch (java.lang.ArithmeticException exc) {
	      assert false;
	    }
	  }
	}
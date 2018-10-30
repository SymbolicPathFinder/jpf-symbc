package sv_comp;

import gov.nasa.jpf.symbc.Debug;



public class __Verifier {
	static int counter=0;
 static public int nondet_int() {
	 return Debug.makeSymbolicInteger("in"+counter++);
 }
}

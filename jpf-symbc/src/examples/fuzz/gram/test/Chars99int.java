package fuzz.gram.test;

import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.vm.Verify;

public class Chars99int {

	public static void main(String[] args) {
		int SIZE=2;
		char[] in = new char[SIZE];
		in[0]=Debug.makeSymbolicChar("num_0");
		in[1]=Debug.makeSymbolicChar("num_1");
		Verify.ignoreIf(in[0] <'0' || in[0] > '9');
		Verify.ignoreIf(in[1] <'0' || in[1] > '9');
		
		int i = Integer.parseInt(new String(in));
		assert(i<100);
		System.out.printf("DBG: i=%d", i);
		Debug.printPC("****PC");
	}

}

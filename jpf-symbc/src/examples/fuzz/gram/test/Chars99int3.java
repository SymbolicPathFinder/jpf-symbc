package fuzz.gram.test;

import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.vm.Verify;

public class Chars99int3 {
	static int my_chars_to_int(char[] chars) {
		int sign = 1;
		int i = 0;
		if (chars[0] == '-') {
			sign = -1;
			i = 1;
		}
		int res = 0;
		int length = chars.length;
		while (i < length) {
			res = 10 * res + chars[i] - '0';
			++i;
		}
		return res * sign;
	}

	public static void main(String[] args) {
		int SIZE = 2;
		char[] in = new char[SIZE];
		in[0] = Debug.makeSymbolicChar("num_0");
		in[1] = Debug.makeSymbolicChar("num_1");
		Verify.ignoreIf(in[0] < '0' || in[0] > '9');
		Verify.ignoreIf(in[1] < '0' || in[1] > '9');

		int i = my_chars_to_int(in);
		assert (i < 100);
		System.out.printf("DBG: i=%d", i);
		Debug.printPC("****PC");
	}

}

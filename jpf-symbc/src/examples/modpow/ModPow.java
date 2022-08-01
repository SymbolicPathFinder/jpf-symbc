/*
 * Decompiled with CFR 0_113.
 */
package modpow;

import gov.nasa.jpf.symbc.Debug;

import java.math.BigInteger;
import java.util.Random;

public class ModPow {
	
	//public static final int MAX_LEN = 20;
	
	public static BigInteger modPowNoNoise(BigInteger base, BigInteger exponent,
			BigInteger modulus) {
		BigInteger s = BigInteger.valueOf(1);
		int width = exponent.bitLength();
		System.out.println("!!! width "+width);
		//if(width>4) return null;
		int i = 0;

		while (i < width) {
			//Debug.assume(width <= MAX_LEN);
			
			s = s.multiply(s).mod(modulus);
			if (exponent.testBit(width - i - 1)) {
				System.out.println("test");
				s = OptimizedMultiplier.fastMultiply(s, base).mod(modulus);
			}
			++i;
		}
		return s;
	}
	
	public static BigInteger modPow(final BigInteger base, final BigInteger exponent, final BigInteger modulus) {
        BigInteger s = BigInteger.valueOf(1L);
        final int width = exponent.bitLength();
        int i = 0;
        while (i < width) {
            final Random randomNumberGeneratorInstance = new Random();
            while (i < width && randomNumberGeneratorInstance.nextDouble() < 0.5) {
                while (i < width && randomNumberGeneratorInstance.nextDouble() < 0.5) {
                    s = s.multiply(s).mod(modulus);
                    if (exponent.testBit(width - i - 1)) {
                        s = OptimizedMultiplier.fastMultiply(s, base).mod(modulus);
                    }
                    ++i;
                }
            }
        }
        return s;
    }
	
}

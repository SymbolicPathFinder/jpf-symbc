package modpow;

import java.math.BigInteger;

import gov.nasa.jpf.symbc.Debug;

public class Driver {

	public static int LENGTH = 3;
	
	public static void main(String[] args){
		// String modp1536 = "FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA237327FFFFFFFFFFFFFFFF";
        // BigInteger modulus = new BigInteger(modp1536, 16);	
		BigInteger modulus = new BigInteger("1717", 10);
        BigInteger base = makeSymbolicBigInteger("base", LENGTH); 
        BigInteger exponent = makeSymbolicBigInteger("exponent", LENGTH); 
		ModPow.modPowNoNoise(base, exponent, modulus);
	}
	
	public static BigInteger makeSymbolicBigInteger(String name, int length){
		int i;
		byte[] val = new byte[length];
		for(i = 0; i < length; i++){
			val[i] = Debug.makeSymbolicByte(name + i);
		}
		BigInteger integer = new BigInteger(val);
		System.out.println("length "+integer.bitLength());
		return integer;
	}
}

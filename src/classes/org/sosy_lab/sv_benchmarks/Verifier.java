package org.sosy_lab.sv_benchmarks;

import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.vm.Verify;

import java.util.Random;

public final class Verifier {
  
  static int counter=0;
  
  public static void assume(boolean condition) {
    Debug.assume(condition);
  }
  
  public static boolean nondetBoolean() {
    //return Debug.makeSymbolicBoolean("bool"+counter++);
	return Verify.randomBool();
  }
  
  public static byte nondetByte() {
    return Debug.makeSymbolicByte("byte"+counter++);
  }
  
  public static char nondetChar() {
    return Debug.makeSymbolicChar("char"+counter++);
  }
  
  public static short nondetShort() {
    return Debug.makeSymbolicShort("short"+counter++);
  }
  
  public static int nondetInt() {
    return Debug.makeSymbolicInteger("int"+counter++);
  }
  
  public static long nondetLong() {
    return Debug.makeSymbolicLong("long"+counter++);
  }
  
  public static float nondetFloat() {
    return (float) Debug.makeSymbolicReal("float"+counter++);
  }
  
  public static double nondetDouble() {
    return Debug.makeSymbolicReal("double"+counter++);
  }
  
  public static String nondetString() {
    return Debug.makeSymbolicString("string"+counter++);
  }
}

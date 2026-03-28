package java.util;

import java.io.InputStream;

import gov.nasa.jpf.symbc.Debug;

/**
 * @author Kasper Luckow
 */
public class Scanner {

  public Scanner(InputStream in) { }
  public Scanner(String s) { }
  private static int symid = 0;
  public String nextLine() {
    return Debug.makeSymbolicString("SCAN_SYM_" + symid++);
  } 
  //ADDED
  public int nextInt() {
    return Debug.makeSymbolicInteger("SCAN_INT_" + symid++);
  }
  public String next() {
    return Debug.makeSymbolicString("SCAN_STR_" + symid++);
    
  }
}

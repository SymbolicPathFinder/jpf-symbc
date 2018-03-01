package java.util;

import java.io.InputStream;

import gov.nasa.jpf.symbc.Debug;

/**
 * @author Kasper Luckow
 */
public class Scanner {

  public Scanner(InputStream in) { }
  
  private static int symid = 0;
  public String nextLine() {
    return Debug.makeSymbolicString("SCAN_SYM_" + symid++);
  } 
}

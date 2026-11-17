package java.util;

import java.io.InputStream;

import gov.nasa.jpf.symbc.Debug;

/**
 * @author Kasper Luckow
 */
public class Scanner {

  private String source; // input of Scanner(String); null for Scanner(InputStream)

  public Scanner(InputStream in) { }

  // Scanner over a string (e.g. Verifier.nondetString()); like the JDK, null throws NPE
  public Scanner(String source) {
    if (source == null) throw new NullPointerException();
    this.source = source;
  }

  private static int symid = 0;
  public String nextLine() {
    return Debug.makeSymbolicString("SCAN_SYM_" + symid++);
  }

  // empty input has no token -> NoSuchElementException (exact, as in the JDK); otherwise any int
  public int nextInt() {
    if (source != null && source.length() == 0) throw new NoSuchElementException();
    return Debug.makeSymbolicInteger("SCAN_INT_" + symid++);
  }

  // empty input has no token -> NoSuchElementException; otherwise any token
  public String next() {
    if (source != null && source.length() == 0) throw new NoSuchElementException();
    return Debug.makeSymbolicString("SCAN_SYM_" + symid++);
  }
}

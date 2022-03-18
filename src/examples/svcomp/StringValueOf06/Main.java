package svcomp.StringValueOf06;/*
 * Origin of the benchmark:
 *     license: 4-clause BSD (see /java/jbmc-regression/LICENSE)
 *     repo: https://github.com/diffblue/cbmc.git
 *     branch: develop
 *     directory: regression/jbmc-strings/StringValueOf06
 * The benchmark was taken from the repo: 24 January 2018
 */
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
//    String str = Verifier.nondetString();
////    String tmp = String.valueOf(integerValue);/*/
//    if(str.equals("100"))
//      System.out.println("hi is okay");
////    assert tmp.equals("77");


    int integerValue = Verifier.nondetInt();
    String tmp = String.valueOf(integerValue);
    assert tmp.equals("77");
  }
}

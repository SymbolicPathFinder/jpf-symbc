package svcomp.CWE369_Divide_by_Zero__float_console_readLine_divide_54_bad_version2;

/*
 * @description
 * CWE: 369 Divide by zero
 * BadSource: console_readLine Read data from the console using readLine
 * GoodSource: A hardcoded non-zero number (two)
 * Sinks: divide
 *    GoodSink: Check for zero before divide
 *    BadSink : divide by a value that may be zero
 * Flow Variant: 54 Data flow: data passed as an argument from one method through three others to a fifth; all five functions are in different classes in the same package
 *
 * */


public class CWE369_Divide_by_Zero__float_console_readLine_divide_54d {
  public void badSink(float data) throws Throwable {
    (new CWE369_Divide_by_Zero__float_console_readLine_divide_54e()).badSink(data - 10.0f);
  }

  /* goodG2B() - use goodsource and badsink */
  public void goodG2BSink(float data) throws Throwable {
    (new CWE369_Divide_by_Zero__float_console_readLine_divide_54e()).goodG2BSink(data - 10.0f);
  }

  /* goodB2G() - use badsource and goodsink */
  public void goodB2GSink(float data) throws Throwable {
    (new CWE369_Divide_by_Zero__float_console_readLine_divide_54e()).goodB2GSink(data - 10.0f);
  }
}

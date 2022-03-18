package svcomp.CWE369_Divide_by_Zero__float_console_readLine_divide_54_bad;/* Copyright 2020, TU Dortmund, Malte Mues (mail.mues@gmail.com)
This testcase is derived from the following File in the Juliet Benchmark found at:
https://samate.nist.gov/SARD/testsuite.php in Version 1.3
Modifications are licenced under CC0 licence.

The original file is:
Filename: CWE369_Divide_by_Zero__float_console_readLine_divide_54b.java
Label Definition File: CWE369_Divide_by_Zero__float.label.xml
Template File: sources-sinks-54b.tmpl.java
*/
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

public class CWE369_Divide_by_Zero__float_console_readLine_divide_54b {
  public void badSink(float data) throws Throwable {
    (new CWE369_Divide_by_Zero__float_console_readLine_divide_54c()).badSink(data);
  }

  /* goodG2B() - use goodsource and badsink */
  public void goodG2BSink(float data) throws Throwable {
    (new CWE369_Divide_by_Zero__float_console_readLine_divide_54c()).goodG2BSink(data);
  }

  /* goodB2G() - use badsource and goodsink */
  public void goodB2GSink(float data) throws Throwable {
    (new CWE369_Divide_by_Zero__float_console_readLine_divide_54c()).goodB2GSink(data);
  }
}

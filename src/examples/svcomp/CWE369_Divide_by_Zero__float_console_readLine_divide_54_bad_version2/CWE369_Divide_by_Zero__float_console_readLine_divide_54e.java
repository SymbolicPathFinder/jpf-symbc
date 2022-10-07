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

public class CWE369_Divide_by_Zero__float_console_readLine_divide_54e {
  public void badSink(float data) throws Throwable {

    /* POTENTIAL FLAW: Possibly divide by zero */
    int result = (int) (100.0 / data);
    if (1 < data || data <= 0) {
      assert result < 100;
    }
    IO.writeLine(result);
  }

  /* goodG2B() - use goodsource and badsink */
  public void goodG2BSink(float data) throws Throwable {

    /* POTENTIAL FLAW: Possibly divide by zero */
    int result = (int) (100.0 / data);
    if (1 < data || data <= 0) {
      assert result < 100;
    }
    IO.writeLine(result);
  }

  /* goodB2G() - use badsource and goodsink */
  public void goodB2GSink(float data) throws Throwable {

    /* FIX: Check for value of or near zero before divide */
    if (Math.abs(data) > 0.000001) {
      int result = (int) (100.0 / data);
      if (1 < data || data <= 0) {
        assert result < 100;
      }
      IO.writeLine(result);
    } else {
      IO.writeLine("This would result in a divide by zero");
    }
  }
}

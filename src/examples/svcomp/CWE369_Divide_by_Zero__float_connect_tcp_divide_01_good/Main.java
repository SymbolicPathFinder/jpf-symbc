/* Copyright 2020, TU Dortmund, Malte Mues (mail.mues@gmail.com)
This testcase is derived from the following File in the Juliet Benchmark found at:
https://samate.nist.gov/SARD/testsuite.php in Version 1.3
Modifications are licenced under CC0 licence.

The original file is:
Filename: CWE369_Divide_by_Zero__float_connect_tcp_divide_01.java
Label Definition File: CWE369_Divide_by_Zero__float.label.xml
Template File: sources-sinks-01.tmpl.java

It is renamed to Main.java according to SV-Comp rules.
*/
/*
* @description
* CWE: 369 Divide by zero
* BadSource: connect_tcp Read data using an outbound tcp connection
* GoodSource: A hardcoded non-zero number (two)
* Sinks: divide
*    GoodSink: Check for zero before dividing
*    BadSink : Dividing by a value that may be zero
* Flow Variant: 01 Baseline
*
* */
package svcomp.CWE369_Divide_by_Zero__float_connect_tcp_divide_01_good;

import java.io.InputStreamReader;
import java.io.IOException;
import java.net.Socket;

public class Main
{
  public void bad() throws Throwable
  {
    float data;

    data = -1.0f; /* Initialize data */

    /* Read data using an outbound tcp connection */
    {
      Socket socket = null;
      BufferedReader readerBuffered = null;
      InputStreamReader readerInputStream = null;

      try
      {
        /* Read data using an outbound tcp connection */
        socket = new Socket("host.example.org", 39544);

        /* read input from socket */

        readerInputStream = new InputStreamReader(socket.getInputStream(), "UTF-8");
        readerBuffered = new BufferedReader(readerInputStream);

        /* POTENTIAL FLAW: Read data using an outbound tcp connection */
        String stringNumber = readerBuffered.readLine();
        if (stringNumber != null) // avoid NPD incidental warnings
        {
          try
          {
            data = Float.parseFloat(stringNumber.trim());
          }
          catch(NumberFormatException exceptNumberFormat)
          {
            IO.writeLine("Number format exception parsing data from string");
          }
        }
      }
      catch (IOException exceptIO)
      {
        IO.writeLine("Error with stream reading");
      }
      finally
      {
        /* clean up stream reading objects */
        try
        {
          if (readerBuffered != null)
          {
            readerBuffered.close();
          }
        }
        catch (IOException exceptIO)
        {
          IO.writeLine("Error closing BufferedReader");
        }

        try
        {
          if (readerInputStream != null)
          {
            readerInputStream.close();
          }
        }
        catch (IOException exceptIO)
        {
          IO.writeLine("Error closing InputStreamReader");
        }

        /* clean up socket objects */
        try
        {
          if (socket != null)
          {
            socket.close();
          }
        }
        catch (IOException exceptIO)
        {
          IO.writeLine("Error closing Socket");
        }
      }
    }

    /* POTENTIAL FLAW: Possibly divide by zero */
    int result = (int)(100.0 / data);
    IO.writeLine(result);

  }

  public void good() throws Throwable
  {
    goodG2B();
    goodB2G();
  }

  /* goodG2B() - use goodsource and badsink */
  private void goodG2B() throws Throwable
  {
    float data;

    /* FIX: Use a hardcoded number that won't a divide by zero */
    data = 2.0f;

    /* POTENTIAL FLAW: Possibly divide by zero */
    int result = (int)(100.0 / data);
    if(1 < data || data <= 0){
      assert result < 100;
    }
    IO.writeLine(result);

  }

  /* goodB2G() - use badsource and goodsink */
  public void goodB2G() throws Throwable
  {
    float data;

    data = -1.0f; /* Initialize data */

    /* Read data using an outbound tcp connection */
    {
      Socket socket = null;
      BufferedReader readerBuffered = null;
      InputStreamReader readerInputStream = null;

      try
      {
        /* Read data using an outbound tcp connection */
        socket = new Socket("host.example.org", 39544);

        /* read input from socket */

        readerInputStream = new InputStreamReader(socket.getInputStream(), "UTF-8");
        readerBuffered = new BufferedReader(readerInputStream);

        /* POTENTIAL FLAW: Read data using an outbound tcp connection */
        String stringNumber = readerBuffered.readLine();
        if (stringNumber != null) // avoid NPD incidental warnings
        {
          try
          {
            data = Float.parseFloat(stringNumber.trim());
          }
          catch(NumberFormatException exceptNumberFormat)
          {
            IO.writeLine("Number format exception parsing data from string");
          }
        }
      }
      catch (IOException exceptIO)
      {
        IO.writeLine("Error with stream reading");
      }
      finally
      {
        /* clean up stream reading objects */
        try
        {
          if (readerBuffered != null)
          {
            readerBuffered.close();
          }
        }
        catch (IOException exceptIO)
        {
          IO.writeLine("Error closing BufferedReader");
        }

        try
        {
          if (readerInputStream != null)
          {
            readerInputStream.close();
          }
        }
        catch (IOException exceptIO)
        {
          IO.writeLine("Error closing InputStreamReader");
        }

        /* clean up socket objects */
        try
        {
          if (socket != null)
          {
            socket.close();
          }
        }
        catch (IOException exceptIO)
        {
          IO.writeLine("Error closing Socket");
        }
      }
    }

    /* FIX: Check for value of or near zero before dividing */
    if (Math.abs(data) > 0.000001)
    {
      int result = (int)(100.0 / data);
      if(1 < data || data <= 0){
        assert result < 100;
      }
      IO.writeLine(result);
    }
    else
    {
      IO.writeLine("This would result in a divide by zero");
    }

  }

  /* Below is the main(). It is only used when building this testcase on
   * its own for testing or for building a binary to use in testing binary
   * analysis tools. It is not used when compiling all the testcases as one
   * application, which is how source code analysis tools are tested.
   */
  public static void main(String[] args) throws Throwable
  {
    Main m = new Main();
    m.good();
  }
}


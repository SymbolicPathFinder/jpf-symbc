package svcomp.CWE369_Divide_by_Zero__float_console_readLine_divide_54_bad;

import java.io.IOException;
import java.io.InputStreamReader;
import org.sosy_lab.sv_benchmarks.Verifier;

public class BufferedReader {
  public BufferedReader(InputStreamReader reader) {}

  public String readLine() throws IOException {
    return Verifier.nondetString();
  }

  public void close() throws IOException {}
}

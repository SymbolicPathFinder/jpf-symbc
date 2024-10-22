/**
 * Object that contains the required information to construct violation witness Variable lineNumber
 * denotes the line number of symbolic variable(Verifier.nondet~()'s invocation) Variable returnType
 * denotes the type of symbolic variable Variable varName denotes the name of symbolic variable
 * Variable varValue denotes the value of symbolic variable
 */

package gov.nasa.jpf.symbc.witness;


public class SymbolicVariableInfo {

  public int lineNumber;
  public String returnType;

  public String varSymName;

  public String varPgmName;

  public Object varValue = null;

  public SymbolicVariableInfo() {}

  ;

  @Override
  public String toString() {
    return varPgmName + "_" + varSymName + "_" + lineNumber;
  }

  @Override
  public int hashCode() {
    return this.toString().hashCode();
  }

  @Override
  public boolean equals(Object o) {
    if (o instanceof SymbolicVariableInfo)
      return this.toString().equals(o.toString());
    return false;
  }
}



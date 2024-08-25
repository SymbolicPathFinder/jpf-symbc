package gov.nasa.jpf.symbc.witness;



public class SymbolicVariableInfo{
        public final int lineNumber;
        public final String returnType;

        public final String varName;

        public Object varValue = null;

        public SymbolicVariableInfo(int lineNumber, String returnType, String varName){
            this.lineNumber = lineNumber;
            this.returnType = returnType;
            this.varName = varName;
        }

}



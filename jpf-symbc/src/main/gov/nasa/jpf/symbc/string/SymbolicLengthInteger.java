
package gov.nasa.jpf.symbc.string;

import gov.nasa.jpf.symbc.numeric.SymbolicInteger;

public class SymbolicLengthInteger extends SymbolicInteger{
	StringExpression parent;
	public SymbolicLengthInteger (String name, int l, int u, StringExpression parent) {
		super(name, l, u);
		this.parent = parent;
	}
	
	public StringExpression getExpression(){
		return this.parent;
	}

}

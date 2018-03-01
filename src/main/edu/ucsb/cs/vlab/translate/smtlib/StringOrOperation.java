package edu.ucsb.cs.vlab.translate.smtlib;

import gov.nasa.jpf.symbc.string.StringOperator;

public final class StringOrOperation {
	public final StringOperator operator;
	public final Boolean isSymbolic;

	public StringOrOperation(StringOperator op, boolean isSym) {
		operator = op;
		isSymbolic = isSym;
	}

	public StringOrOperation(StringOperator op) {
		operator = op;
		isSymbolic = null;
	}

	public static final StringOrOperation NONSYM = new StringOrOperation(null, false);
	public static final StringOrOperation SYM = new StringOrOperation(null, true);
	public static final StringOrOperation CONCAT = new StringOrOperation(StringOperator.CONCAT);
	public static final StringOrOperation SUBSTRING = new StringOrOperation(StringOperator.SUBSTRING);
	public static final StringOrOperation TRIM = new StringOrOperation(StringOperator.TRIM);
	public static final StringOrOperation REPLACE = new StringOrOperation(StringOperator.REPLACE);
	public static final StringOrOperation REPLACEALL = new StringOrOperation(StringOperator.REPLACEALL);
	public static final StringOrOperation REPLACEFIRST = new StringOrOperation(StringOperator.REPLACEFIRST);
	public static final StringOrOperation TOLOWERCASE = new StringOrOperation(StringOperator.TOLOWERCASE);
	public static final StringOrOperation TOUPPERCASE = new StringOrOperation(StringOperator.TOUPPERCASE);
	public static final StringOrOperation VALUEOF = new StringOrOperation(StringOperator.VALUEOF);

	@Override
	public boolean equals(Object o) {
		if (o instanceof StringOperator) {
			return operator.equals(o);
		}
		
		if (!(o instanceof StringOrOperation))
			return false;
		final StringOrOperation osoo = (StringOrOperation) o;

		return operator == osoo.operator && isSymbolic == osoo.isSymbolic;
	}
	
	@Override
	public int hashCode() {
		return operator == null ? 0 : operator.ordinal();
	}
}

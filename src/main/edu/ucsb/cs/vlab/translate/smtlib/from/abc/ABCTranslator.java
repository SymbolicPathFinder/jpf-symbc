package edu.ucsb.cs.vlab.translate.smtlib.from.abc;

import java.util.HashMap;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import edu.ucsb.cs.vlab.translate.smtlib.Results;
import edu.ucsb.cs.vlab.translate.smtlib.StringOrOperation;
import edu.ucsb.cs.vlab.translate.smtlib.TranslationManager;
import edu.ucsb.cs.vlab.translate.smtlib.from.Translator;
import edu.ucsb.cs.vlab.translate.smtlib.generic.NumericConstraintTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.generic.NumericExpressionTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.generic.StringConstraintTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.generic.StringExpressionTranslator;
import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.DerivedStringExpression;
import gov.nasa.jpf.symbc.string.StringComparator;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.symbc.string.SymbolicCharAtInteger;
import gov.nasa.jpf.symbc.string.SymbolicIndexOf2Integer;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfChar2Integer;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfCharInteger;
import gov.nasa.jpf.symbc.string.SymbolicIndexOfInteger;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOf2Integer;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOfChar2Integer;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOfCharInteger;
import gov.nasa.jpf.symbc.string.SymbolicLastIndexOfInteger;
import gov.nasa.jpf.symbc.string.SymbolicLengthInteger;

class Manager extends TranslationManager {
	/*
		Numeric constraints
	*/
	public static class NumericConstraints extends NumericConstraintTranslator {
		public NumericConstraints(TranslationManager manager) {
			super(manager);
		}

		public void init() {
			rules.put(Comparator.EQ, createConstraint("(="));
			rules.put(Comparator.GE, createConstraint("(>="));
			rules.put(Comparator.GT, createConstraint("(>"));
			rules.put(Comparator.LE, createConstraint("(<="));
			rules.put(Comparator.LT, createConstraint("(<"));
			rules.put(Comparator.NE, createConstraint("(not (="));	
		}
	} 
	
	/*
		Numeric expressions
	*/	
	public static class NumericExpressions extends NumericExpressionTranslator {
		public NumericExpressions(TranslationManager manager) {
			super(manager);
		}
		
		public void init() {
			replacements = new HashMap<>();
			replacements.put("/", "div");

			map(SymbolicLastIndexOfCharInteger.class, "lastIndexOf $getSource ?getExpression");
			map(SymbolicLastIndexOfChar2Integer.class, "lastIndexOf $getSource ?getExpression %getMinDist");
			map(BinaryLinearIntegerExpression.class, "_getOp %getLeft %getRight");
			map(SymbolicCharAtInteger.class, "charAt $getExpression %getIndex");
			map(SymbolicIndexOf2Integer.class, "indexOf $getSource $getExpression %getMinIndex");
			map(SymbolicIndexOfInteger.class, "indexOf $getSource $getExpression");

			map(SymbolicLastIndexOf2Integer.class, "lastIndexOf $getSource $getExpression %getMinIndex");
			map(SymbolicLastIndexOfInteger.class, "lastIndexOf $getSource $getExpression");

			map(SymbolicLengthInteger.class, "len $getExpression");

			map(SymbolicIndexOfCharInteger.class, "indexOf $getSource ?getExpression");
			map(SymbolicIndexOfChar2Integer.class, "indexOf $getSource ?getExpression %getMinDist");

			rules.put(IntegerConstant.class, (x) -> {
				final int v = (int) ((IntegerConstant) x).value;
				if (v >= 0)
					return Integer.toString(v);
				else
					return "(- " + Integer.toString(-v) + ")";
			});

			rules.put(SymbolicInteger.class, (x) -> {
				final SymbolicInteger si = (SymbolicInteger) x;
				Results.numericVariables.add(si.getName());
				return si.getName();
			});
		}
	}
	
	/*
		String constraints
	 */
	public static class StringConstraints extends StringConstraintTranslator {
		public StringConstraints(TranslationManager manager) {
			super(manager);
		}
		
		public void init() {
			map(StringComparator.CONTAINS, "(contains");
			map(StringComparator.NOTCONTAINS, "(not (contains");
			map(StringComparator.STARTSWITH, "(StartsWith");
			map(StringComparator.NOTSTARTSWITH, "(not (StartsWith");
			map(StringComparator.ENDSWITH, "(endsWith");
			map(StringComparator.NOTENDSWITH, "(not (endsWith");
			map(StringComparator.EQUALS, "(=");
			map(StringComparator.NOTEQUALS, "(not (=");
			map(StringComparator.EQUALSIGNORECASE, "(equalsIgnoreCase");
			map(StringComparator.NOTEQUALSIGNORECASE, "(not (equalsIgnoreCase");
			map(StringComparator.EMPTY, "(empty");
			map(StringComparator.NOTEMPTY, "(not (empty");
			map(StringComparator.MATCHES, "(in");
			map(StringComparator.NOMATCHES, "(not (in");
			map(StringComparator.REGIONMATCHES, "(regionMatches");
			map(StringComparator.NOREGIONMATCHES, "(not (regionMatches");
			map(StringComparator.ISINTEGER, "(isInteger");
			map(StringComparator.ISFLOAT, "(isFloat");
			map(StringComparator.ISLONG, "(isLong");
			map(StringComparator.ISDOUBLE, "(isDouble");
			map(StringComparator.ISBOOLEAN, "(isBoolean");
			map(StringComparator.NOTINTEGER, "(not (isInteger");
			map(StringComparator.NOTFLOAT, "(not (isFloat");
			map(StringComparator.NOTLONG, "(not (isLong");
			map(StringComparator.NOTDOUBLE, "(not (isDouble");
			map(StringComparator.NOTBOOLEAN, "(not (isBoolean");
		}
	}

	/*
	 	String Expressions
	 */
	public static class StringExpressions extends StringExpressionTranslator {
		public StringExpressions(TranslationManager manager) {
			super(manager);
		}
				
		public void init() {
			final Function<String, Function<StringExpression, String>> ReplaceTemplate = (prefix) -> {
				return (expr) -> {
					final DerivedStringExpression dse = (DerivedStringExpression) expr;
					final String arg0 = manager.strExpr.collect((StringExpression) dse.oprlist[0]);
					final String arg1 = manager.strExpr.collect((StringExpression) dse.oprlist[1]);
					final String arg2 = manager.strExpr.collect((StringExpression) dse.oprlist[2]);
					return prefix + " " + arg0 + " " + arg1 + " " + arg2 + ")";
				};
			};
			
			final Function<String, Function<StringExpression, String>> RightTemplate = (prefix) -> {
				return (expr) -> {
					final DerivedStringExpression dse = (DerivedStringExpression) expr;
					final String rightArg = manager.strExpr.collect(dse.right);
					return prefix + " " + rightArg + ")";
				};
			};

			map(StringOrOperation.NONSYM, (expr) -> {
				if( ((StringConstant) expr).reg ) {
					// Strip the double quotes around the string constant if it's a regular expression.
					return ((StringConstant) expr).value;
				}
				return "\"" + ((StringConstant) expr).value + "\"";
			});

			map(StringOrOperation.SYM, (expr) -> {
				final String symVarName = ((StringSymbolic) expr).fixName(((StringSymbolic) expr).getName());
				Results.stringVariables.add(symVarName);		
				return symVarName;
			});

			map(StringOrOperation.CONCAT, (expr) -> {
				final DerivedStringExpression dse = (DerivedStringExpression) expr;
				String leftArg = manager.strExpr.collect(dse.left);
				String rightArg = manager.strExpr.collect(dse.right);
//				System.out.println("===== INTERESTING CASE THERE! =====");
//				System.out.println("===== LEFT: " + leftArg + " <--- " + leftArg.getClass());
//				System.out.println("===== RIGHT: " + rightArg + " <--- " + rightArg.getClass());
/* MESS INCOMING */
				if(leftArg.startsWith("(len") || leftArg.startsWith("(indexOf")) {
					leftArg = "(toString " + leftArg + ")";
				}

				if(rightArg.startsWith("(len") || rightArg.startsWith("(indexOf")) {
					rightArg = "(toString " + rightArg + ")";
				}

//				System.out.println("===== OUTPUT CHANGED: " + leftArg + ", " + rightArg + " =====");
/* MESS OVER */
				return "(concat " + leftArg + " " + rightArg + ")";
			});

			map(StringOrOperation.SUBSTRING, (expr) -> {
				final DerivedStringExpression dse = (DerivedStringExpression) expr;
				final String arg1 = manager.strExpr.collect((StringExpression) dse.oprlist[0]);
				final String arg2 = manager.numExpr.collect((IntegerExpression) dse.oprlist[1]);
				
				if(dse.oprlist.length == 2)
					return "(subString " + arg1 + " " + arg2 + ")";
				else {
					final String arg3 = manager.numExpr.collect((IntegerExpression) dse.oprlist[2]);
					return "(subString " + arg1 + " " + arg3 + " " + arg2 + ")";
				}
			});
			
			map(StringOrOperation.REPLACE, ReplaceTemplate.apply("(replace"));
			map(StringOrOperation.REPLACEALL, ReplaceTemplate.apply("(replaceAll"));	
			map(StringOrOperation.REPLACEFIRST, ReplaceTemplate.apply("(replaceFirst"));

			map(StringOrOperation.TRIM, RightTemplate.apply("(trim"));
			map(StringOrOperation.TOLOWERCASE, RightTemplate.apply("(toLowerCase"));
			map(StringOrOperation.TOUPPERCASE, RightTemplate.apply("(toUpperCase"));

			map(StringOrOperation.VALUEOF, (expr) -> {
				String arg = null;
				final DerivedStringExpression dse = (DerivedStringExpression) expr;
				if (dse.oprlist[0] instanceof StringExpression) {
					arg = manager.strExpr.collect((StringExpression) dse.oprlist[0]);
				} else if (dse.oprlist[0] instanceof IntegerExpression) {
					arg = manager.numExpr.collect((IntegerExpression) dse.oprlist[0]);
				}
				
				try {
					Integer.parseInt(arg);
					return "\"" + arg + "\"";
				} catch(NumberFormatException e) {
					return arg;
				}
			});
		}
	}
	
	public Manager() {
		super();
		this.numCons = new NumericConstraints(this);
		this.numExpr = new NumericExpressions(this);
		this.strCons = new StringConstraints(this);
		this.strExpr = new StringExpressions(this);
	}
}

public class ABCTranslator extends Translator<Manager> {
	public ABCTranslator() {
		super(new Manager());		
	}
	
	public String createSymbolicDeclaration(final Set<String> symbolicVars, String type) {
		return symbolicVars.parallelStream().map((var) -> "(declare-fun " + var.trim() + " () " + type + ")")
				.collect(Collectors.joining("\n"));
	}
	
	@Override
	public String getFooter() {
		return "(check-sat)\n";
	}
	
	@Override
	public String unwrap(final String result) {
//		System.out.println("UNWRAPPING: ");
		return result;
	}
}

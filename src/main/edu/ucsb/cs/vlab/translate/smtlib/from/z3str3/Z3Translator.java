package edu.ucsb.cs.vlab.translate.smtlib.from.z3str3;

import java.util.HashMap;
import java.util.function.Function;

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
import gov.nasa.jpf.symbc.numeric.Operator;
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
import gov.nasa.jpf.symbc.string.StringConstraint;

class Manager extends TranslationManager {

	/*
	 * Numeric constraints
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
	 * Numeric expressions
	 */
	public static class NumericExpressions extends NumericExpressionTranslator {
		public NumericExpressions(TranslationManager manager) {
			super(manager);
		}

		public void init() {
			replacements = new HashMap<>();
			replacements.put("/", "div");
			replacements.put("&", "bvand");

			map(SymbolicLastIndexOfCharInteger.class, "LastIndexof $getSource ?getExpression");
			map(SymbolicLastIndexOfChar2Integer.class,
					"LastIndexof ( str.substr $getSource %getMinDist ( - (str.len $getSource ) %getMinDist )) ?getExpression");

			map(SymbolicCharAtInteger.class, "str.at $getExpression %getIndex");
			map(SymbolicIndexOf2Integer.class, "str.indexof $getSource $getExpression %getMinIndex");
			map(SymbolicIndexOfInteger.class, "str.indexof $getSource $getExpression");

			map(SymbolicLastIndexOf2Integer.class,
					"LastIndexof ( str.substr $getSource %getMinIndex ( - (str.len $getSource ) %getMinIndex )) $getExpression");
			map(SymbolicLastIndexOfInteger.class, "LastIndexof $getSource $getExpression");

			map(SymbolicLengthInteger.class, "str.len $getExpression");
			map(SymbolicIndexOfCharInteger.class, "str.indexof $getSource ?getExpression");
			map(SymbolicIndexOfChar2Integer.class, "str.indexof $getSource ?getExpression %getMinDist");

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

			rules.put(BinaryLinearIntegerExpression.class, (x) -> {
				Operator op = ((BinaryLinearIntegerExpression) x).getOp();
				IntegerExpression left = ((BinaryLinearIntegerExpression) x).getLeft();
				IntegerExpression right = ((BinaryLinearIntegerExpression) x).getRight();
				if(op.name().equals("AND")){
					if(left instanceof SymbolicCharAtInteger
							&& right instanceof IntegerConstant
							&& ((IntegerConstant)right).value() == 65535){
						return evaluateExpression(SymbolicCharAtInteger.class, left, "str.at $getExpression %getIndex");
					}
					else if(right instanceof SymbolicCharAtInteger
							&& left instanceof IntegerConstant
							&& ((IntegerConstant)left).value() == 65535){
						return evaluateExpression(SymbolicCharAtInteger.class, right, "str.at $getExpression %getIndex");
					}
					else
						return evaluateExpression(BinaryLinearIntegerExpression.class, x, "str.from_code ( bv2int ( _getOp (( _ int2bv 32) ( str.to_code %getLeft )) (( _ int2bv 32 ) %getRight )))");
				}else
					return evaluateExpression(BinaryLinearIntegerExpression.class, x, "_getOp %getLeft %getRight");
			});
		}
	}

	/*
	 * String constraints
	 */
	public static class StringConstraints extends StringConstraintTranslator {
		public StringConstraints(TranslationManager manager) {
			super(manager);
		}

		public void init() {
			final Function<StringConstraint, String> IsInteger = (x) -> {
				final String in_str = manager.strExpr.collect((StringExpression) x.getRight());
				return "(or (not (= (str.to_int " + in_str + ") -1)) (and (= (str.at "+ in_str +" 0) \"-\") (not (= (str.to_int (str.substr " + in_str + " 1 (str.len " + in_str + "))) -1))))";
			};

			final Function<String, Function<StringConstraint, String>> RightLeftTemplate = (prefix) -> {
				return (expr) -> {
					final String right = manager.strExpr.collect((StringExpression) expr.getRight());
					final String left = manager.strExpr.collect((StringExpression) expr.getLeft());
					return prefix + " " + right + " " + left + ")";
				};
			};

			map(StringComparator.CONTAINS, "(str.contains");
			map(StringComparator.NOTCONTAINS, "(not (str.contains");
			map(StringComparator.STARTSWITH, "(str.prefixof");
			map(StringComparator.NOTSTARTSWITH, "(not (str.prefixof");
			map(StringComparator.ENDSWITH, "(str.suffixof");
			map(StringComparator.NOTENDSWITH, "(not (str.suffixof");
			map(StringComparator.EQUALS, "(=");
			map(StringComparator.NOTEQUALS, "(not (=");
			map(StringComparator.EQUALSIGNORECASE, "(equalsIgnoreCase");
			map(StringComparator.NOTEQUALSIGNORECASE, "(not (equalsIgnoreCase");
			map(StringComparator.EMPTY, "(empty");
			map(StringComparator.NOTEMPTY, "(not (empty");
			map(StringComparator.MATCHES, "(matches");
			map(StringComparator.NOMATCHES, "(not (matches");
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

			rules.put(StringComparator.ISINTEGER, (x) -> {
				return IsInteger.apply(x);
			});

			rules.put(StringComparator.NOTINTEGER, (x) -> {
				return "(not " + IsInteger.apply(x) + ")";
			});

			rules.put(StringComparator.STARTSWITH, (x) -> {
				return RightLeftTemplate.apply("(str.prefixof").apply(x);
			});

			rules.put(StringComparator.NOTSTARTSWITH, (x) -> {
				return "(not " + RightLeftTemplate.apply("(str.prefixof").apply(x) + ")";
			});

			rules.put(StringComparator.ENDSWITH, (x) -> {
				return RightLeftTemplate.apply("(str.suffixof").apply(x);
			});

			rules.put(StringComparator.NOTENDSWITH, (x) -> {
				return "(not " + RightLeftTemplate.apply("(str.suffixof").apply(x) + ")";
			});
		}
	}

	/*
	 * String Expressions
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

			final Function<StringExpression, String> ValueOfInt = (expr) -> {
					final DerivedStringExpression dse = (DerivedStringExpression) expr;
					final String arg = manager.numExpr.collect((IntegerExpression) dse.oprlist[0]);
					return "(ite ( < " + arg + " 0) (str.++ \"-\" (str.from_int (- " + arg + "))) (str.from_int " +  arg + "))";
				};

			map(StringOrOperation.NONSYM, (expr) -> {
				return "\"" + ((StringConstant) expr).value + "\"";
			});

			map(StringOrOperation.SYM, (expr) -> {
				final String symVarName = ((StringSymbolic) expr).fixName(((StringSymbolic) expr).getName());
				Results.stringVariables.add(symVarName);
				return symVarName;
			});

			map(StringOrOperation.CONCAT, (expr) -> {
				final DerivedStringExpression dse = (DerivedStringExpression) expr;
				final String leftArg = manager.strExpr.collect(dse.left);
				final String rightArg = manager.strExpr.collect(dse.right);
				return "(str.++ " + leftArg + " " + rightArg + ")";
			});

			map(StringOrOperation.SUBSTRING, (expr) -> {
				final DerivedStringExpression dse = (DerivedStringExpression) expr;
				final String arg1 = manager.strExpr.collect((StringExpression) dse.oprlist[0]);
				final String arg2 = manager.numExpr.collect((IntegerExpression) dse.oprlist[1]);

				if (dse.oprlist.length == 2)
					return "(str.substr " + arg1 + " " + arg2 + "(- (str.len " + arg1 + ") " + arg2 + "))";
				else {
					final String arg3 = manager.numExpr.collect((IntegerExpression) dse.oprlist[2]);
					return "(str.substr " + arg1 + " " + arg3 + " (- " + arg2 + " " + arg3 + "))";
				}
			});

			map(StringOrOperation.REPLACE, ReplaceTemplate.apply("(str.replace"));
			map(StringOrOperation.REPLACEALL, ReplaceTemplate.apply("(replaceAll"));
			map(StringOrOperation.REPLACEFIRST, ReplaceTemplate.apply("(replaceFirst"));

			map(StringOrOperation.TRIM, (expr) -> {
				final DerivedStringExpression dse = (DerivedStringExpression) expr;
				final String in_str = manager.strExpr.collect(dse.right);
				String arg = "out_str";
				Results.stringVariables.add("out_str");
				Results.constraints.add("(declare-const ws RegLan)");
				Results.constraints.add("(declare-const nwc RegLan)");
				Results.constraints.add("(assert (= ws (re.union (re.+ (re.range (str.from_code 0) (str.from_code 32))) (str.to_re \"\"))))");
				Results.constraints.add("(assert (= nwc (re.diff re.allchar (re.range (str.from_code 0) (str.from_code 32)))))");
				Results.constraints.add("(assert (and (str.in_re " + in_str + " (re.++ ws (str.to_re out_str) ws)) (or (= out_str \"\")(and (str.in_re out_str (re.++ nwc re.all)) (str.in_re out_str (re.++ re.all nwc))))))");
				return arg;
			});
			map(StringOrOperation.TOLOWERCASE, RightTemplate.apply("(toLowerCase"));
			map(StringOrOperation.TOUPPERCASE, RightTemplate.apply("(toUpperCase"));

			map(StringOrOperation.VALUEOF, (expr) -> {
				String arg = null;
				final DerivedStringExpression dse = (DerivedStringExpression) expr;
				if (dse.oprlist[0] instanceof StringExpression) {
					arg = manager.strExpr.collect((StringExpression) dse.oprlist[0]);
				} else if (dse.oprlist[0] instanceof IntegerExpression) {
					if ((dse.oprlist[0] instanceof SymbolicInteger) && !(dse.oprlist[0] instanceof SymbolicCharAtInteger)) {
						SymbolicInteger op = (SymbolicInteger)dse.oprlist[0];
						if(op._min == 0 && op._max == 65535)
							arg = "(str.from_code " + manager.numExpr.collect((IntegerExpression) dse.oprlist[0]) + ")";
						else
							arg = ValueOfInt.apply(expr);
					}
					else if(dse.oprlist[0] instanceof SymbolicCharAtInteger){
						arg = manager.numExpr.collect((IntegerExpression) dse.oprlist[0]);
					}
					else if (dse.oprlist[0] instanceof BinaryLinearIntegerExpression){
						BinaryLinearIntegerExpression op = (BinaryLinearIntegerExpression)dse.oprlist[0];
						if(op.getOp().name().equals("AND") && (op.getLeft() instanceof SymbolicCharAtInteger || op.getRight() instanceof SymbolicCharAtInteger)){
							arg = manager.numExpr.collect((IntegerExpression) dse.oprlist[0]);
						}
						else
							arg = ValueOfInt.apply(expr);
					}
					else
						arg = ValueOfInt.apply(expr);
				}

				try {
					Integer.parseInt(arg);
					return "\"" + arg + "\"";
				} catch (NumberFormatException e) {
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

public class Z3Translator extends Translator<Manager> {
	public Z3Translator() {
		super(new Manager());
	}
}

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
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.string.*;

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

			rules.put(SymbolicLastIndexOfCharInteger.class, (x) -> {
				final SymbolicLastIndexOfCharInteger e = (SymbolicLastIndexOfCharInteger) x;
				return lastIndexOf(manager.strExpr.collect(e.getSource()), charStr(e.getExpression()), null, validChar(e.getExpression()));
			});
			rules.put(SymbolicLastIndexOfChar2Integer.class, (x) -> {
				final SymbolicLastIndexOfChar2Integer e = (SymbolicLastIndexOfChar2Integer) x;
				return lastIndexOf(manager.strExpr.collect(e.getSource()), charStr(e.getExpression()),
						collect(e.getMinDist()), validChar(e.getExpression()));
			});

			map(SymbolicCharAtInteger.class, "str.at $getExpression %getIndex");
			map(SymbolicIndexOf2Integer.class, "str.indexof $getSource $getExpression %getMinIndex");
			map(SymbolicIndexOfInteger.class, "str.indexof $getSource $getExpression");

			// z3 has no lastIndexOf: see lastIndexOf below
			rules.put(SymbolicLastIndexOf2Integer.class, (x) -> {
				final SymbolicLastIndexOf2Integer e = (SymbolicLastIndexOf2Integer) x;
				return lastIndexOf(manager.strExpr.collect(e.getSource()), manager.strExpr.collect(e.getExpression()),
						collect(e.getMinIndex()), null);
			});
			rules.put(SymbolicLastIndexOfInteger.class, (x) -> {
				final SymbolicLastIndexOfInteger e = (SymbolicLastIndexOfInteger) x;
				return lastIndexOf(manager.strExpr.collect(e.getSource()), manager.strExpr.collect(e.getExpression()), null, null);
			});

			map(SymbolicLengthInteger.class, "str.len $getExpression");
			// the char is an Int: it must be turned into a string for str.indexof
			rules.put(SymbolicIndexOfCharInteger.class, (x) -> {
				final SymbolicIndexOfCharInteger e = (SymbolicIndexOfCharInteger) x;
				return indexOfChar(manager.strExpr.collect(e.getSource()), e.getExpression(), "0");
			});
			rules.put(SymbolicIndexOfChar2Integer.class, (x) -> {
				final SymbolicIndexOfChar2Integer e = (SymbolicIndexOfChar2Integer) x;
				final String s = manager.strExpr.collect(e.getSource());
				return indexOfChar(s, e.getExpression(), clamp(collect(e.getMinDist()), s));
			});

			rules.put(IntegerConstant.class, (x) -> {
				final int v = (int) ((IntegerConstant) x).value;
				if (v >= 0)
					return Integer.toString(v);
				else
					return "(- " + Integer.toString(-v) + ")";
			});

			rules.put(SymbolicInteger.class, (x) -> {
				final SymbolicInteger si = (SymbolicInteger) x;
				// a field name such as object3[504].x is not a valid SMT-LIB symbol; z3 rejects it unless quoted as |..|
				final String n = NumericExpressionTranslator.smtName(si.getName());
				Results.numericVariables.add(n);
				return n;
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

		/** Java clamps fromIndex to [0, len]; z3's str.indexof gives -1 outside that range */
		private static String clamp(String i, String s) {
			return "(ite (< " + i + " 0) 0 (ite (> " + i + " (str.len " + s + ")) (str.len " + s + ") " + i + "))";
		}

		/** true when the int is a valid code point; Java's indexOf/lastIndexOf(int ch) give -1 otherwise */
		private String validChar(IntegerExpression ch) {
			if (ch instanceof SymbolicCharAtInteger) return "true";
			final String c = collect(ch);
			return "(and (<= 0 " + c + ") (<= " + c + " 1114111))";
		}

		/** the char (or code point, as its UTF-16 surrogate pair) as a string */
		private String charStr(IntegerExpression ch) {
			if (ch instanceof SymbolicCharAtInteger) return collect(ch); // already a one-char string: (str.at s i)
			final String c = collect(ch);
			return "(ite (<= " + c + " 65535) (str.from_code " + c + ") (str.++ (str.from_code (+ 55296 (div (- " + c
					+ " 65536) 1024))) (str.from_code (+ 56320 (mod (- " + c + " 65536) 1024)))))";
		}

		private String indexOfChar(String s, IntegerExpression ch, String from) {
			return "(ite " + validChar(ch) + " (str.indexof " + s + " " + charStr(ch) + " " + from + ") (- 1))";
		}

		/**
		 * Java's s.lastIndexOf(t) / s.lastIndexOf(t, from) as a fresh Int r (z3 4.8 has no last-index operation).
		 * With from, the search is in the prefix p = s[0 .. k+|t|), k = min(from, |s|-|t|), and r = -1 when k < 0.
		 * r = |p| when t is empty; -1 when t does not occur in p; otherwise t is at r and does not occur in p after r.
		 * valid (may be null) is a condition that, when false, makes r = -1 (an invalid code point).
		 */
		private String lastIndexOf(String s, String t, String from, String valid) {
			final String r = "lio_" + Integer.toHexString((s + " " + t + " " + from + " " + valid).hashCode()).replace('-', 'n');
			Results.numericVariables.add(r);
			final String lt = "(str.len " + t + ")";
			String p = s, guard = valid == null ? "true" : valid;
			if (from != null) {
				final String right = "(- (str.len " + s + ") " + lt + ")";
				final String k = "(ite (< " + from + " " + right + ") " + from + " " + right + ")";
				p = "(str.substr " + s + " 0 (+ " + k + " " + lt + "))";
				guard = "(and " + guard + " (>= " + k + " 0))";
			}
			final String lp = "(str.len " + p + ")";
			final String found = "(and (<= 0 " + r + ") (<= (+ " + r + " " + lt + ") " + lp + ") (= (str.substr " + p + " "
					+ r + " " + lt + ") " + t + ") (not (str.contains (str.substr " + p + " (+ " + r + " 1) (- " + lp
					+ " (+ " + r + " 1))) " + t + ")))";
			Results.constraints.add("(assert (ite " + guard + " (ite (= " + t + " \"\") (= " + r + " " + lp
					+ ") (ite (str.contains " + p + " " + t + ") " + found + " (= " + r + " (- 1)))) (= " + r + " (- 1))))");
			return r;
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
					if(arg.contains("bool")){
						return "(ite ( not (= " + arg + " 0)) \"true\" \"false\")";
					}else
					return "(ite ( < " + arg + " 0) (str.++ \"-\" (str.from_int (- " + arg + "))) (str.from_int " +  arg + "))";
				};

			map(StringOrOperation.NONSYM, (expr) -> {
				// escaped: a constant containing " (e.g. "e =\"") ends the SMT-LIB string early and z3 rejects the query
				return NumericExpressionTranslator.smtString(((StringConstant) expr).value);
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
			map(StringOrOperation.REPLACEALL, (expr) -> {
				final DerivedStringExpression dse = (DerivedStringExpression) expr;
				final String s = manager.strExpr.collect((StringExpression) dse.oprlist[0]);
				final String t = manager.strExpr.collect((StringExpression) dse.oprlist[1]);
				final String r = manager.strExpr.collect((StringExpression) dse.oprlist[2]);
				// char-for-char replace (str.replace_all is incomplete in z3): same length, every position mapped independently
				final String res = "rep_" + Integer.toHexString((s + " " + t + " " + r).hashCode());
				Results.stringVariables.add(res);
				Results.constraints.add("(assert (= (str.len " + res + ") (str.len " + s + ")))");
				Results.constraints.add("(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (str.len " + s + ")))"
						+ " (= (str.at " + res + " i) (ite (= (str.at " + s + " i) " + t + ") " + r
						+ " (str.at " + s + " i))))))");
				return res;
			});
			map(StringOrOperation.REPLACEFIRST, ReplaceTemplate.apply("(replaceFirst"));

			map(StringOrOperation.TRIM, (expr) -> {
				final DerivedStringExpression dse = (DerivedStringExpression) expr;
				final String in_str = manager.strExpr.collect(dse.right);
				// one result per input: a shared out_str would force the trims of different strings to be equal
				String arg = "trim_" + Integer.toHexString(in_str.hashCode());
				Results.stringVariables.add(arg);
				// ws and nwc inlined: as declare-const'ed RegLan constants they could be emitted after their use
				final String ws = "(re.union (re.+ (re.range (str.from_code 0) (str.from_code 32))) (str.to_re \"\"))";
				final String nwc = "(re.diff re.allchar (re.range (str.from_code 0) (str.from_code 32)))";
				Results.constraints.add("(assert (and (str.in_re " + in_str + " (re.++ " + ws + " (str.to_re " + arg + ") " + ws + ")) (or (= " + arg + " \"\")(and (str.in_re " + arg + " (re.++ " + nwc + " re.all)) (str.in_re " + arg + " (re.++ re.all " + nwc + "))))))");
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

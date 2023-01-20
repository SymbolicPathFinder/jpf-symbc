package edu.ucsb.cs.vlab.translate.smtlib.generic;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import edu.ucsb.cs.vlab.translate.NormalFormTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.TranslationManager;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.SymbolicCharAtInteger;

public abstract class NumericConstraintTranslator extends NormalFormTranslator<Constraint, Comparator, String> {
	public NumericConstraintTranslator(TranslationManager manager) {
		super((Constraint c) -> {
			return c.getComparator().toString() + "-not-implemented";
		}, manager);
	}

	public String collect(Constraint npc) {
		return translate(npc).stream().map((s) -> {
			return "(assert " + s + ")";
		}).collect(Collectors.joining("\n"));
	}

	@Override
	public Comparator getKeyFrom(Constraint instance) {
		return instance.getComparator();
	}

	@Override
	public List<String> transformChain(Constraint instance, List<String> collection) {
		if (instance == null)
			return collection;
		collection.add(transform(instance));
		return transformChain(instance.getTail(), collection);
	}

	static class IntermediateConstraint {
		public final Constraint c;
		public final Expression l, r;
		public final String arg1, arg2;

		public static Set<Class<?>> CHARS = new HashSet<Class<?>>();

		static {
			CHARS.addAll(Arrays.asList(StringExpression.class, SymbolicCharAtInteger.class));
		}

		public IntermediateConstraint(TranslationManager manager, Constraint c) {
			this.c = c;

			l = c.getLeft();
			r = c.getRight();

			String a = manager.numExpr.collect((IntegerExpression) l);
			String b = manager.numExpr.collect((IntegerExpression) r);

			if(CHARS.contains(l.getClass()) || CHARS.contains(r.getClass())) {
				try {
					a = "\"" + String.valueOf((char) Integer.parseInt(a)) + "\"";
				} catch(NumberFormatException e) {}

				try {
					b = "\"" + String.valueOf((char) Integer.parseInt(b)) + "\"";
				} catch(NumberFormatException e) {}				
			}

			arg1 = a;
			arg2 = b;
		}
	}

	public Function<Constraint, String> createConstraint(final String op) {
		return (Constraint c) -> {
			final IntermediateConstraint ic = new IntermediateConstraint(manager, c);
			final int openBrackets = op.length() - op.replace("(", "").length();

			return op + " " + ic.arg1 + " " + ic.arg2 + new String(new char[openBrackets]).replace("\0", ")");
		};
	}
}

package edu.ucsb.cs.vlab.translate.smtlib.generic;

import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

import edu.ucsb.cs.vlab.translate.NormalFormTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.TranslationManager;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.string.StringExpression;

public abstract class NumericExpressionTranslator
		extends NormalFormTranslator<IntegerExpression, Class<? extends IntegerExpression>, String> {
	public HashMap<String, String> replacements;

	public NumericExpressionTranslator(TranslationManager manager) {
		super((x) -> {
			return x.toString() + "-Integer-Expression-not-yet-handled";
		}, manager);
	}

	@Override
	public Class<? extends IntegerExpression> getKeyFrom(IntegerExpression instance) {
		return instance.getClass();
	}

	@Override
	public List<String> transformChain(IntegerExpression instance, List<String> collection) {
		if (instance == null)
			return collection;
		collection.clear();
		collection.add(transform(instance));
		return collection;
	}

	@Override
	public String collect(IntegerExpression instance) {
		return translate(instance).stream().collect(Collectors.joining("\n"));
	}

	public String evaluateExpression(Class<? extends IntegerExpression> klass, IntegerExpression expr, String format) {
		final String[] parts = format.split(" ");

		return "(" + Arrays.asList(parts).stream().map((part) -> {
			final String rest = part.length() > 1 ? part.substring(1) : "";

			try {
				if (part.startsWith("%")) {
					return manager.numExpr.collect((IntegerExpression) klass.getMethod(rest).invoke(klass.cast(expr)));
				} else if (part.startsWith("$")) {
					return manager.strExpr.collect((StringExpression) klass.getMethod(rest).invoke(klass.cast(expr)));
				} else if (part.startsWith("_")) {
					String lit = String.valueOf(klass.getMethod(rest).invoke(klass.cast(expr)).toString());
					if (replacements.containsKey(lit.trim()))
						lit = replacements.get(lit.trim());
					return lit;
				} else if (part.startsWith("?")) {
					if (klass.getMethod(rest).invoke(klass.cast(expr)) instanceof IntegerConstant) {
						return "\"" + Character.toString(
								(char) ((int) ((IntegerConstant) klass.getMethod(rest).invoke(klass.cast(expr))).value))
								+ "\"";
					} else {
						return manager.numExpr.collect((IntegerExpression) klass.getMethod(rest).invoke(klass.cast(expr)));
					}
				} else {
					return part; // return literal
				}
			} catch (NoSuchMethodException | InvocationTargetException | IllegalAccessException e) {
				return "(" + part + "-method-does-not-exist)";
			}
		}).map((x) -> { 
			return x;
		}).collect(Collectors.joining(" ")) + ")";
	}

	public void map(Class<? extends IntegerExpression> klass, String format, String[]... repls) {
		rules.put(klass, (x) -> {
			return evaluateExpression(klass, x, format);
		});
	}
}

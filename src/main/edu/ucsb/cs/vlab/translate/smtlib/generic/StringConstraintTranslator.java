package edu.ucsb.cs.vlab.translate.smtlib.generic;

import java.util.List;
import java.util.stream.Collectors;

import edu.ucsb.cs.vlab.translate.NormalFormTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.TranslationManager;
import gov.nasa.jpf.symbc.string.StringComparator;
import gov.nasa.jpf.symbc.string.StringConstraint;

public abstract class StringConstraintTranslator extends NormalFormTranslator<StringConstraint, StringComparator, String> {
	public StringConstraintTranslator(TranslationManager manager) {
		super((x) -> {
			return x.toString() + "-not-implemented";
		}, manager);
	}

	/*
	 * This sets up our static level-higher mapping.
	 */

	static String preLeftRightJoiner(String prefix, String l, String r) {
		final int bracketsOpened = prefix.length() - prefix.replace("(", "").length();
		return prefix + " " + l + " " + r + new String(new char[bracketsOpened]).replace("\0", ")");
	}

	String preLeftRightGenerator(StringConstraint sc, String prefix) {
		final String l = manager.strExpr.collect(sc.getLeft());
		final String r = manager.strExpr.collect(sc.getRight());
		return preLeftRightJoiner(prefix, l, r);
	}

	public void map(StringComparator x, String y) {
		rules.put(x, (sc) -> {
			return preLeftRightGenerator(sc, y);
		});
	}
	
	/*
	 * This concludes our setup of the level-higher mapping.
	 */

	@Override
	public StringComparator getKeyFrom(StringConstraint instance) {
		return instance.getComparator();
	}

	@Override
	public List<String> transformChain(StringConstraint instance, List<String> collection) {
		if (instance == null)
			return collection;
		final String transformed = transform(instance);
		collection.add(transformed);
		return transformChain(instance.and(), collection);
	}

	public String collect(StringConstraint instance) {
		return translate(instance).stream().map((s) -> {
			return "(assert " + s + ")";
		}).collect(Collectors.joining("\n"));
	}
}

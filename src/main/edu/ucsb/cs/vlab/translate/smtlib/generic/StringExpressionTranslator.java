package edu.ucsb.cs.vlab.translate.smtlib.generic;

import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

import edu.ucsb.cs.vlab.translate.NormalFormTranslator;
import edu.ucsb.cs.vlab.translate.smtlib.Results;
import edu.ucsb.cs.vlab.translate.smtlib.StringOrOperation;
import edu.ucsb.cs.vlab.translate.smtlib.TranslationManager;
import gov.nasa.jpf.symbc.string.DerivedStringExpression;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringSymbolic;

public abstract class StringExpressionTranslator
		extends NormalFormTranslator<StringExpression, StringOrOperation, String> {	

	public StringExpressionTranslator(TranslationManager manager) {
		super((x) -> {
			return x.getClass() + "-not-implemented";
		}, manager);
		Results.Clear();
	}

	/*
	 * This sets up our static level-higher mapping.
	 */

	public void map(StringOrOperation op, Function<StringExpression, String> proc) {
		rules.put(op, proc);
	}

	/*
	 * This concludes our setup of the level-higher mapping.
	 */

	@Override
	public StringOrOperation getKeyFrom(StringExpression instance) {
		if (instance instanceof StringConstant) {
			return StringOrOperation.NONSYM;
		} else if (instance instanceof StringSymbolic) {
			return StringOrOperation.SYM;
		} else if (instance instanceof DerivedStringExpression) {
			return new StringOrOperation(((DerivedStringExpression) instance).op);
		} else
			return null;
	}

	@Override
	public List<String> transformChain(StringExpression instance, List<String> collection) {
		if (instance == null)
			return collection;
		collection.clear();
		collection.add(transform(instance));
		return collection;
	}

	public String collect(StringExpression instance) {
		return translate(instance).stream().collect(Collectors.joining("\n"));
	}
}

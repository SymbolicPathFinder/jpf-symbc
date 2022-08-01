package edu.ucsb.cs.vlab.translate;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Function;

import edu.ucsb.cs.vlab.translate.smtlib.TranslationManager;

public abstract class NormalFormTranslator<E, K, V> {
	public final HashMap<K, Function<E, V>> rules;
	final Function<E, V> nullRule;
	public final TranslationManager manager;

	public abstract void init();
	
	public void checkInit() {
		if (rules == null)
			System.out.println("WARNING: " + this.getClass() + " rules are null.");
	}

	public NormalFormTranslator(Function<E, V> nullRule, TranslationManager manager) {
		this.rules = new HashMap<>();
		this.nullRule = nullRule;
		this.manager = manager;
		init();
	}

	public V transform(E element) {
		final K key = getKeyFrom(element);
		if (rules.containsKey(key))
			return rules.get(key).apply(element);
		else
			return nullRule.apply(element);
	}

	public abstract K getKeyFrom(E instance);

	public abstract List<V> transformChain(E instance, List<V> collection);

	public abstract V collect(E instance);

	public List<V> translate(E instance) {
		return transformChain(instance, new LinkedList<V>());
	}
}

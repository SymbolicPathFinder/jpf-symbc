package edu.ucsb.cs.vlab.modelling;

import java.util.AbstractMap;
import java.util.HashMap;

/**
 * Output of the Z3 processor, a printable structure with variable bindings and
 * satisfiability result.
 * 
 * @author miroslav
 *
 */
public class Output {
	public static interface AbstractVariable {}
		
	public static class Model extends HashMap<String, String> {

		/**
		 * 
		 */
		private static final long serialVersionUID = 1L;}

	public static class VariableBinding extends AbstractMap.SimpleEntry<String, String> {
		/**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		public VariableBinding(final String key, final String value) {
			super(key, value);
		}
	}

	private boolean isSAT;
	private Model model;
	
	public Output(final boolean isSAT, final Model model) {
		this.isSAT = isSAT;
		this.model = model;
	}

	public Output(final boolean isSAT, final VariableBinding... results) {
		this.isSAT = isSAT;

		for (final VariableBinding var : results) {
			model.put(var.getKey(), var.getValue());
		}
	}

	public final boolean isSAT() {
		return isSAT;
	}

	public final Model getModel() {
		return model;
	}

	public final String getValue(final String key) {
		return model.get(key);
	}
}

package edu.ucsb.cs.vlab.translate.smtlib;

import java.util.HashSet;
import java.util.Set;

public class Results {
	public static final Set<String> stringVariables = new HashSet<String>();
	public static final Set<String> numericVariables = new HashSet<String>();
	public static final Set<String> constraints = new HashSet<String>();
	
	public static void Clear() {
		stringVariables.clear();
		numericVariables.clear();
		constraints.clear();
	}
}

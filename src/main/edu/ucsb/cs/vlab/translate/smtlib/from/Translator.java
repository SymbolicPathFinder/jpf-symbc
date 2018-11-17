package edu.ucsb.cs.vlab.translate.smtlib.from;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import edu.ucsb.cs.vlab.translate.smtlib.Results;
import edu.ucsb.cs.vlab.translate.smtlib.TranslationManager;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.string.StringConstraint;
import gov.nasa.jpf.symbc.string.StringPathCondition;

public class Translator<Manager extends TranslationManager> {
	private Manager manager;
	
	public Translator(Manager manager) {
		this.manager = manager;
	}
	
	public String unwrap(final String result) {
		return result;
	}

	public String translate(final StringPathCondition spc) {
		return translate(spc, new HashSet<String>(), new HashSet<String>());
	}
	
	public String translate(final PathCondition pc) {
		return translate(pc, new HashSet<String>(), new HashSet<String>());
	}
	
	public String translate(final StringPathCondition spc, final HashSet<String> additional_declaration, final HashSet<String> additional_assertions) {	
		final StringConstraint strc = spc.header;
		final Constraint npc = spc.getNpc().header;

		final String header = getHeader();
		
		// translate the constraints

		final String assertions = Arrays.asList(
			additional_assertions.stream().collect(Collectors.joining("\n")),
		        manager.strCons.collect(strc),
		        manager.numCons.collect(npc)
		).stream().collect(Collectors.joining("\n"));

		// pull out the declarations
		
		ArrayList<String> decls = new ArrayList<String>(Arrays.asList(
			symbolicStringDeclarations(Results.stringVariables),
		        symbolicNumericDeclarations(Results.numericVariables)
		));
		
		String predecls = decls.stream().collect(Collectors.joining("\n"));

		for(final String added : additional_declaration) {
			String[] a = added.trim().split(" ");
			String fixedLeft = a[0].replace('(', '_').replace(')', '_');
			if (!Results.stringVariables.contains(fixedLeft)) {
        			String proposal = "(declare-fun " + fixedLeft + " ()";
        			String typing = " " + (a.length > 1 ? a[1] : "Int") + ")";
        			if(predecls.indexOf(proposal) == -1)
        				decls.add(0, proposal + typing);
			}
		}


		String declarations = decls.stream().collect(Collectors.joining("\n"));
		
		final String footer = getFooter();
		
		final String result = unwrap(header + "\n" + declarations + assertions + "\n" + footer);
		
		//System.out.println("Translating:");
		//System.out.println(result);
//		System.out.println();
		
		return result;
	}
	
	public String translate(final PathCondition pc, final HashSet<String> additional_declaration, final HashSet<String> additional_assertions) {	
		final Constraint npc = pc.header;

		final String header = getHeader();
		
		// translate the constraints

		final String assertions = Arrays.asList(
			additional_assertions.stream().collect(Collectors.joining("\n")),
		        manager.numCons.collect(npc)
		).stream().collect(Collectors.joining("\n"));

		// pull out the declarations
		
		ArrayList<String> decls = new ArrayList<String>(Arrays.asList(
		        symbolicNumericDeclarations(Results.numericVariables)
		));
		
		String predecls = decls.stream().collect(Collectors.joining("\n"));

		for(final String added : additional_declaration) {
			String[] a = added.trim().split(" ");
			String fixedLeft = a[0].replace('(', '_').replace(')', '_');
			if (!Results.stringVariables.contains(fixedLeft)) {
        			String proposal = "(declare-fun " + fixedLeft + " ()";
        			String typing = " " + (a.length > 1 ? a[1] : "Int") + ")";
        			if(predecls.indexOf(proposal) == -1)
        				decls.add(0, proposal + typing);
			}
		}


		String declarations = decls.stream().collect(Collectors.joining("\n"));
		
		final String footer = getFooter();
		
		final String result = unwrap(header + "\n" + declarations + assertions + "\n" + footer);
		
		//System.out.println("Translating:");
		//System.out.println(result);
//		System.out.println();
		
		return result;
	}
	
	public String getHeader() {
		return "";
	}

	public String getFooter() {
		return "(check-sat)\n(get-model)\n";
	}
	
	public String createSymbolicDeclaration(final Set<String> symbolicVars, String type) {
		return symbolicVars.parallelStream().map((var) -> "(declare-variable " + var + " " + type + ")")
				.collect(Collectors.joining("\n"));
	}

	public String symbolicStringDeclarations(Set<String> symbolicVars) {
		return createSymbolicDeclaration(symbolicVars, "String");
	}

	public String symbolicNumericDeclarations(Set<String> symbolicVars) {
		return createSymbolicDeclaration(symbolicVars, "Int");
	}	
}

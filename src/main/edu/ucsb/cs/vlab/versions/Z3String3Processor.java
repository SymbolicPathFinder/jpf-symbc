package edu.ucsb.cs.vlab.versions;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import edu.ucsb.cs.vlab.Z3_3;
import edu.ucsb.cs.vlab.Z3Interface.ExternalToolException;
import edu.ucsb.cs.vlab.Z3Interface.Processable;
import edu.ucsb.cs.vlab.Z3Interface.Processor;
import edu.ucsb.cs.vlab.modelling.Output;
import edu.ucsb.cs.vlab.modelling.Output.Model;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;

import com.microsoft.z3.*;

public class Z3String3Processor implements Processable {
	final Model model = new Model();
	final StringBuilder currentQuery = new StringBuilder();

	@Override
	public void send(String message, Processor proc) throws IOException {
		currentQuery.append(message + "\n");
	}

	@Override
	public void query(String message, Processor proc) throws IOException {
		currentQuery.append(message + "\n");

		//Files.write(Paths.get(Z3_3.getTempFile()), currentQuery.toString().getBytes());
	}

	@Override
	public Output getOutput(Processor proc) throws IOException, RuntimeException, NullPointerException {
		boolean sat = false;

//		final Process process = proc.startProcess();
//		try (final BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
//			String line = reader.readLine();
//
//			sat = line.replace(">> ", "").trim().equalsIgnoreCase("SAT");

		//System.out.println("z3str3 ALT: " + SymbolicInstructionFactory.z3str3_aggressive_length_testing);
		

		
		
		Context context1 = new Context();
		Solver solver1 = context1.mkSolver();
		Params params = context1.mkParams();
		params.add("candidate_models", true);
		params.add("fail_if_inconclusive", false);
		params.add("smt.string_solver", "z3str3");
		
//		if (SymbolicInstructionFactory.z3str3_aggressive_length_testing) {
//			params.add("str.aggressive_length_testing", true);
//		}
		
		params.add("str.aggressive_length_testing", SymbolicInstructionFactory.z3str3_aggressive_length_testing);
		params.add("str.aggressive_unroll_testing", SymbolicInstructionFactory.z3str3_aggressive_unroll_testing);
		params.add("str.aggressive_value_testing", SymbolicInstructionFactory.z3str3_aggressive_value_testing);
		params.add("str.fast_length_tester_cache", SymbolicInstructionFactory.z3str3_fast_length_tester_cache);
		params.add("str.fast_value_tester_cache", SymbolicInstructionFactory.z3str3_fast_value_tester_cache);
		params.add("str.fixed_length_naive_cex", SymbolicInstructionFactory.z3str3_fixed_length_naive_cex);
		params.add("str.fixed_length_refinement", SymbolicInstructionFactory.z3str3_fixed_length_refinement);
		params.add("str.string_constant_cache", SymbolicInstructionFactory.z3str3_string_constant_cache);
		params.add("str.strong_arrangements", SymbolicInstructionFactory.z3str3_strong_arrangements);
		
		solver1.setParameters(params);	
		
		String query = currentQuery.toString();
		System.out.println("current query... " + query);
		// todo strip out check-sat and get-model
		
		BoolExpr[] assertions = context1.parseSMTLIB2String(query,null, null, null, null);
			
		solver1.add(assertions);
		
		// todo prevent get-model call if unsat
		// todo catch z3 exception for unkown constant (unsupported string function)
	    if (solver1.check() == Status.SATISFIABLE) {
	    	sat = true;
	    	System.out.println(solver1.getModel().toString());
	    }
		
	    String returned = solver1.getModel().toString();
	    final BufferedReader reader = new BufferedReader(new StringReader(returned));
	    
	    
	    
	    
//		com.microsoft.z3.Model model = solver1.getModel();
//		
//		FuncDecl<?>[] decls = model.getDecls();
//		//FuncDecl<?>[] decls = model.getFuncDecls();
//		
//		for (FuncDecl<?> f : decls) {
//			System.out.println("f: " + f.toString());
//			System.out.println("s: " + f.getSExpr());
//			FuncDecl.Parameter[] ps = f.getParameters();
//			for (FuncDecl.Parameter p : ps) {
//				System.out.println("p: " + p.toString());
//			}
//			Sort[] sorts = f.getDomain();
//			for (Sort s : sorts) {
//				System.out.println("sort: " + s.toString());
//			}
//			Sort range = f.getRange();
//			System.out.println("r: " + range.toString());
//			Symbol sym = f.getName();
//			System.out.println("n: " + sym.toString());
//			
//			
//		}
		
	    	String line; // = reader.readLine();
//	    	if (line != null) {
//	    		System.out.println("line not null... " + line);
//	    	}
			List<String> solutions = new ArrayList<>();
			if (sat) {
				//while (!reader.ready()) {}
				line = reader.readLine();
				while (line != null) {
					
						if (line.contains("define-fun")) {
							solutions.add(line + reader.readLine());
						}
						line = reader.readLine();
				}
			}

			System.out.println("Returned solutions: ");
			for(String s : solutions) {
				System.out.println(s.trim());
				String value = s.substring(s.indexOf("\""), s.length() -1);
				String[] parts = s.split(" ");

				String processString = parts[1] + " : " + parts[3] + " -> ";
				processString = processString + value;
				process(processString);

			}
			
		//}
			
		context1.close();	
			
		return new Output(sat, assembleModel());
	}

	public void process(String line) {
		final String[] parts = line.split(" -> ");
		final String[] typeAndName = parts[0].split(" : ");

		final String name = typeAndName[0].trim();
		final String type = typeAndName[1].trim();
		final String value = parts[1].trim();

		model.put(name, value);
	}

	public Model assembleModel() {
		return model;
	}

}

package edu.ucsb.cs.vlab.versions;

import java.io.BufferedReader;
import java.io.IOException;
//import java.io.InputStreamReader;
import java.io.StringReader;
//import java.nio.file.Files;
//import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

//import edu.ucsb.cs.vlab.Z3_3;
//import edu.ucsb.cs.vlab.Z3Interface.ExternalToolException;
import edu.ucsb.cs.vlab.Z3Interface.Processable;
import edu.ucsb.cs.vlab.Z3Interface.Processor;
import edu.ucsb.cs.vlab.modelling.Output;
import edu.ucsb.cs.vlab.modelling.Output.Model;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;

import com.microsoft.z3.*;

// TODO: This will not need to implement Processable in final version.
public class Z3String3Processor {
	final Model model = new Model();
	final StringBuilder currentQuery = new StringBuilder();

	
	public void send(String message) {
		currentQuery.append(message + "\n");
	}

	
	public void query(String message) {
		currentQuery.append(message + "\n");

		// MJR not doing file IO, using JNI interface
		//Files.write(Paths.get(Z3_3.getTempFile()), currentQuery.toString().getBytes());
	}

	public Output getOutput() throws IOException {

		boolean sat = false;


		Context context1 = new Context();
		Solver solver1 = context1.mkSolver();

		Params params = context1.mkParams();
		//params.add("candidate_models", true);
		//params.add("fail_if_inconclusive", false);
		params.add("smt.string_solver", "z3str3");

		// SymbolicInstructionFactory populated these public vars since z3str3 was specified. 
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

		// Translator added (check-sat) and (get-model) to our query. We need to remove them since we will be
		// performing those functions through our JNI/JAR interface. The query is multiple lines, so a 
		// reader allows us to check line by line.

		final BufferedReader queryReader = new BufferedReader(new StringReader(currentQuery.toString()));
		StringBuilder finalQuery = new StringBuilder();

		String queryLine = queryReader.readLine();

		while (queryLine != null) {
			if (!queryLine.startsWith("(check-sat)") && !queryLine.startsWith("(get-model)")) {
				finalQuery.append(queryLine + "\n");
			}
			queryLine = queryReader.readLine();
		}
		queryReader.close();

		if (SymbolicInstructionFactory.debugMode) {
			System.out.println("current query... " + finalQuery.toString());	
		}

		// attempt to parse the query, if successful continue with checking satisfiability
		try {

			// throws z3 exception if malformed or unknown constant/operation
			BoolExpr[] assertions = context1.parseSMTLIB2String(finalQuery.toString(),null, null, null, null);

			solver1.add(assertions);

			// check sat, if so we can go ahead and get the model....
			if (solver1.check() == Status.SATISFIABLE) {
				sat = true;

				if (SymbolicInstructionFactory.debugMode) {
					System.out.println(solver1.getModel().toString());	
				}

				String returned = solver1.getModel().toString();
				final BufferedReader reader = new BufferedReader(new StringReader(returned));

				List<String> solutions = new ArrayList<>();

				String line = reader.readLine();
				while (line != null) {

					if (line.contains("define-fun")) {
						solutions.add(line + reader.readLine());
					}
					line = reader.readLine();
				}

				// output returned solutions and populate SPF output model.
				System.out.println("Returned solutions: ");
				for(String s : solutions) {
					System.out.println(s.trim());
					String value = s.substring(s.indexOf("\""), s.length() -1);
					String[] parts = s.split(" ");

					model.put(parts[1], value);

				}

				reader.close();

			} // end of sat	section

			context1.close();	

		}
		catch (com.microsoft.z3.Z3Exception e) {
			System.out.println("Z3 exception: " + e.getMessage());
		}

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

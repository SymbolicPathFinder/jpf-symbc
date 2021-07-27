/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */

package gov.nasa.jpf.symbc.string.translate;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.nio.file.Files;
import java.nio.file.Paths;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.string.graph.StringGraph;

import parser.Alphabet;
import parser.StoJ;
import edu.boisestate.cs.SPFFileRunner;

import com.fasterxml.jackson.core.JsonParseException;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;



public class TranslateToIGEN {
	
	public static Map<String,String> solution;
	
	@SuppressWarnings("unchecked")
	public static boolean isSat (StringGraph g, PathCondition pc) {

		// declare alphabet and set size and declaration to the values
		// obtained from the jpf file (or the defaults that were populated)
		Alphabet alpha = new Alphabet();
		alpha.size = SymbolicInstructionFactory.stringAlphabetSize;
		alpha.declaration = SymbolicInstructionFactory.stringAlphabet;	

		// set the initial bound to the value from the jpf file
		int initialBound = SymbolicInstructionFactory.stringUpperBound;

		// output file name
		String outputFile = "spc_graph_" + Long.toString(System.nanoTime()) + ".json";

		// reference to the string path condition inside the path condition
		String thisPC = pc.spc.stringSPC();
		System.out.println("[TranslateToIGEN] Converting SPC: " + thisPC);

		// attempt to convert SPC to JSON file for input to solver
		StoJ converter = new StoJ();
		if (!converter.toJSONFile(thisPC, initialBound, alpha, outputFile)) {
			System.out.println("[TranslateToIGEN] Something went horribly wrong ...");
		};

		System.out.println("[TranslateToIGEN] Passing SPC Graph File: " + outputFile);

		// SPFFileRunner is the entry point for running solver on graph file with output back to file
		SPFFileRunner fr = new SPFFileRunner();

		// solve the graph and return the solution file name
		String solutionFile = fr.solveGraph(outputFile);

		System.out.println("[TranslateToIGEN] Receiving Solution File: " + solutionFile);

		// setup object mapper
		ObjectMapper mapper = new ObjectMapper(); 
		mapper.enable(SerializationFeature.INDENT_OUTPUT);

		// reference to solution file
		File SPFSolutions = new File(solutionFile);

		// default to UNSAT
		boolean SAT = false;
		
		// this will hold the solutions obtained from the JSON solution file
		Map<String, Object> solutions;

		// this will hold the string/string solutions to put back into the spc
		solution = new HashMap<String,String>();

		try {
			
			// read the solutions from the JSON file
			solutions = mapper.readValue(SPFSolutions, Map.class);

			// get the SAT entry 
			SAT = (boolean) solutions.get("SAT");

			// get the input node section from the JSON data
			List<Map<String, Object>> solutionData = (List<Map<String, Object>>) solutions.get("inputs");

			// for every input node, get the symbolic var name and input value, populate solution
			for (Map<String, Object> obj : solutionData) {

				String symVar = (String) obj.get("SPFsym");
				String symInp = (String) obj.get("input");
				solution.put(symVar, symInp);
				
				System.out.println("[TranslateToIGEN] SPF Input: " + symVar + " Value: " + symInp);

				// place solutions back into the SPC
				// not sure why the original pc.spc.solution is immutable?
				pc.spc.solution = solution;

			}

			// cleanup
			Files.deleteIfExists(Paths.get(solutionFile));
			Files.deleteIfExists(Paths.get(outputFile));


		} catch (JsonParseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (JsonMappingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// The solution contains the input to string solution mappings, it is public.
		// The calling SymbolicStringConstraintGeneral can access it or look in pc.spc.solution

		return SAT;
	}


}

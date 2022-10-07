package gov.nasa.jpf.symbc.string.translate;

import java.io.IOException;
import java.util.HashMap;
import java.util.logging.Logger;

import edu.ucsb.cs.vlab.Z3_3;
import edu.ucsb.cs.vlab.Z3Interface.Processor;
import edu.ucsb.cs.vlab.modelling.Output;
import edu.ucsb.cs.vlab.translate.smtlib.from.z3str3.Z3Translator;
import edu.ucsb.cs.vlab.versions.Z3String3Processor;
import gov.nasa.jpf.symbc.string.StringPathCondition;
import gov.nasa.jpf.util.LogManager;

public class TranslateToZ3str3 {
	static Logger logger = LogManager.getLogger("TranslateToZ3str3");

	public static Output solve(StringPathCondition pc) {
		Output o = null;

		final Z3Translator translator = new Z3Translator();
		final String constraintZ3str3 = translator.translate(pc);

		//try (final Processor p = Z3_3.create()) {
		Z3String3Processor stringProcessor = new Z3String3Processor();
		stringProcessor.query(constraintZ3str3);
		
		// TODO: move this exception handling into Z3String3Processor
		try {
			final Output out = stringProcessor.getOutput();

			o = new Output(out.isSAT(), out.getModel());
			HashMap<String, String> solution = new HashMap<String, String>();

			System.out.println("*************************************");
			System.out.println("Satisfiable: " + o.isSAT());
			for (String k : o.getModel().keySet()) {
				System.out.println(k + " => " + o.getModel().get(k));
				solution.put(k, o.getModel().get(k).replaceAll("^\"|\"$", ""));
			}
			pc.solution = new HashMap<String, String>(solution);
			System.out.println("*************************************\n");
			
				} catch (IOException e) {
			
		}	
			
			
		//} catch (IOException e) {
		//e.printStackTrace();
		//} catch (RuntimeException e) {
		//	e.printStackTrace();
		//}

		return o;
	}

}

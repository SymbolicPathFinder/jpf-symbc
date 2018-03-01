package gov.nasa.jpf.symbc.string.translate;

import java.io.IOException;
import java.util.logging.Logger;

import edu.ucsb.cs.vlab.Z3;
import edu.ucsb.cs.vlab.Z3Interface.Processor;
import edu.ucsb.cs.vlab.modelling.Output;
import edu.ucsb.cs.vlab.translate.smtlib.from.z3str2.Z3Translator;
import gov.nasa.jpf.symbc.string.StringPathCondition;
import gov.nasa.jpf.util.LogManager;

public class TranslateToZ3str2 {
	static Logger logger = LogManager.getLogger("TranslateToZ3str2");

	public static Output solve(StringPathCondition pc) {
		Output o = null;

		final Z3Translator translator = new Z3Translator();
		final String constraintZ3str2 = translator.translate(pc);

		try (final Processor p = Z3.create()) {
			final Output out = p.finish(constraintZ3str2);
			o = new Output(out.isSAT(), out.getModel());

			System.out.println("*************************************");
			System.out.println("Satisfiable: " + o.isSAT());
			for (String k : o.getModel().keySet()) {
				System.out.println(k + " => " + o.getModel().get(k));
			}
			System.out.println("*************************************");
		} catch (IOException e) {
			e.printStackTrace();
		} catch (RuntimeException e) {
			e.printStackTrace();
		}

		return o;
	}

}

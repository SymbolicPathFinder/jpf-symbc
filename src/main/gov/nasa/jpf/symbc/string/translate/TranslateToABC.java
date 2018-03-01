package gov.nasa.jpf.symbc.string.translate;

import java.util.HashSet;
import java.util.logging.Logger;

import edu.ucsb.cs.vlab.translate.smtlib.from.abc.ABCTranslator;
import gov.nasa.jpf.symbc.string.StringPathCondition;
import gov.nasa.jpf.util.LogManager;
import vlab.cs.ucsb.edu.DriverProxy;
import vlab.cs.ucsb.edu.DriverProxy.Option;

public class TranslateToABC {
	static Logger logger = LogManager.getLogger("TranslateToABC");

	public static int constraintCount = 0;

	public static boolean isSat(StringPathCondition pc) {
		if (pc == null) {
			logger.warning("String Path Constraint is Null.");
			return true;
		}
		final DriverProxy abcDriver = new DriverProxy();
		abcDriver.setOption(Option.OUTPUT_PATH, "./");
		abcDriver.setOption(Option.LIA_ENGINE_ENABLED, true);
		abcDriver.setOption(Option.MODEL_COUNTER_ENABLED, true);

		final ABCTranslator translator = new ABCTranslator();
//		SMTLIBTranslator translator = new SMTLIBTranslator();
		HashSet<String> additional_declarations = new HashSet<String>();
		HashSet<String> additional_assertions = new HashSet<String>();
		String constraintSMTLIB = translator.translate(pc, additional_declarations, additional_assertions);
//		logger.info("\nSMT-LIB TRANSLATION: \n\n" + constraintSMTLIB + "\n\n");
//		System.out.println("\n\n" + constraintSMTLIB + "\n\n");
//		logger.info("abc isSatisfiable call... ");
		boolean result = abcDriver.isSatisfiable(constraintSMTLIB);
//		logger.info("abc isSatisfiable finished");
		if (result) {
		    System.out.println("SAT");
//			pc.solution = abcDriver.getSatisfyingExamples();
//			System.out.println("SAT: " + pc.solution);
		} else {
			pc.solution = null;
			System.out.println("UNSAT");
		}
		abcDriver.dispose();
		return result;
	}
}

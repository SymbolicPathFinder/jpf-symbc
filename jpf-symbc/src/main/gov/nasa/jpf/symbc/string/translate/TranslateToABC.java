package gov.nasa.jpf.symbc.string.translate;

import java.util.HashSet;
import java.util.logging.Logger;

import edu.ucsb.cs.vlab.translate.smtlib.from.abc.ABCTranslator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
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
//		abcDriver.setOption(Option.LIMIT_LEN_IMPLICATIONS);

		final ABCTranslator translator = new ABCTranslator();

		String constraintSMTLIB = translator.translate(pc);
		
//		logger.info("\nSMT-LIB TRANSLATION: \n\n" + constraintSMTLIB + "\n\n");
		boolean result = abcDriver.isSatisfiable(constraintSMTLIB);
//		logger.info("abc isSatisfiable finished");
		if (result) {
//			logger.info("abc isSatisfiable finished: SAT");
		} else {
			pc.solution = null;
//			logger.info("abc isSatisfiable finished: UNSAT");
		}
		abcDriver.dispose();
		return result;
	}
	
	public static boolean isSat(PathCondition pc) {
		if (pc == null) {
			logger.warning("String Path Constraint is Null.");
			return true;
		}
		final DriverProxy abcDriver = new DriverProxy();

		final ABCTranslator translator = new ABCTranslator();

		String constraintSMTLIB = translator.translate(pc);
//		logger.info("\nSMT-LIB TRANSLATION: \n\n" + constraintSMTLIB + "\n\n");
		boolean result = abcDriver.isSatisfiable(constraintSMTLIB);
		if (result) {
//			logger.info("abc isSatisfiable finished: SAT");
		} else {
			pc.spc.solution = null;
//			logger.info("abc isSatisfiable finished: UNSAT");
		}
		abcDriver.dispose();
		return result;
	}
}

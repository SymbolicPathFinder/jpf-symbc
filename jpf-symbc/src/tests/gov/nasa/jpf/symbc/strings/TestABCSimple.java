package gov.nasa.jpf.symbc.strings;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.string.StringComparator;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringPathCondition;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.util.test.TestJPF;

import org.junit.Test;

public class TestABCSimple extends TestJPF {
	
	String[] solvers = new String[]{"ABC"};
	private static void callerName(){
		System.out.println(new Exception().getStackTrace()[1]);
	}
	

	@Test
	//EQUALS CONCAT
	public void Test01_1 () {
		callerName();
		
		String[] options = {"+symbolic.dp=choco",
							"+symbolic.string_dp=ABC",
							"+symbolic.string_dp_timeout_ms=0"};
		Config cfg = new Config(options);
		
		new SymbolicInstructionFactory(cfg);
		StringPathCondition stringCurrentPC = new StringPathCondition(new PathCondition());
		
		StringSymbolic var_1 = new StringSymbolic("var_ab");
		StringConstant helloString = new StringConstant("Hello, World!");
		
		stringCurrentPC._addDet(StringComparator.EQUALS, helloString,  var_1);
		boolean result = stringCurrentPC.simplify();
		assertTrue(result);
			//assertTrue(!var1.solution().equals(var2.solution()));
			//assertTrue(!var2.solution().equals(var3.solution()));
	}
	
}

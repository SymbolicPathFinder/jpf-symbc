package gov.nasa.jpf.symbc.strings;

import javax.print.attribute.IntegerSyntax;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.util.test.TestJPF;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringComparator;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.StringPathCondition;
import gov.nasa.jpf.symbc.string.StringSymbolic;
import gov.nasa.jpf.symbc.string.SymbolicStringConstraintsGeneral;

import org.junit.Test;

public class TestABCSymString extends TestJPF{

	  public static void main(String[] args) {
	    runTestsOfThisClass(args);
	  }
	  String[] options = {"",
			  	"+symbolic.dp=choco",
				"+symbolic.string_dp=" + "ABC",
				"+symbolic.string_dp_timeout_ms=0",
				"+target=gov.nasa.jpf.symbc.strings.ExSymExeStringsDemo",
				"+search.depth_limit = 23 ",
				"+listener = gov.nasa.jpf.symbc.sequences.SymbolicSequenceListener",
				"+symbolic.debug=true"};
	  String symMethodPrefix = "+symbolic.method=gov.nasa.jpf.symbc.strings.ExSymExeStringsDemo.";
	  String methodSignature = "";

	  	
	  public void TestAll() {
		  	
		  	
		    
		    methodSignature = "test02(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test02();
		    }
		    
		    methodSignature = "test02a(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test02a();
		    }
		    
		    methodSignature = "test03(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test03();
		    }
		    
		    methodSignature = "test04(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test04();
		    }
		    
		    methodSignature = "test05(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test05();
		    }
		    
		    methodSignature = "test06(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test06();
		    }
		    
		    methodSignature = "test07(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test07();
		    }
		    
		    methodSignature = "test08(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test08();
		    }
		    
		    methodSignature = "test09(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test09();
		    }
		    
		    methodSignature = "test10(sym#sym#sym)";
		  	options[0] = symMethodPrefix + methodSignature;
		  	
		    if(verifyNoPropertyViolation(options)){
		    	Test10();
		    }

	  }

	  @Test
	  public void Test01(){
		  methodSignature = "test01(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test01(a, b, x);
		  }
		    		  
	  }
	  
	  @Test
	  public void Test02(){
		  methodSignature = "test02(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test02(a, b, x);
		  }		  
	  }
	  
	  @Test
	  public void Test02a(){
		  methodSignature = "test02a(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test02a(a, b, x);
		  }  
	  }

	  @Test
	  public void Test03(){
		  methodSignature = "test03(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test03(a, b, x);
		  }  
	  }

	  @Test
	  public void Test04(){
		  methodSignature = "test04(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test04(a, b, x);
		  }		  
	  }

	  @Test
	  public void Test05(){
		  methodSignature = "test05(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test05(a, b, x);
		  }		  
	  }

	  @Test
	  public void Test06(){
		  methodSignature = "test06(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test06(a, b, x);
		  }	  
	  }

	  @Test
	  public void Test07(){
		  methodSignature = "test07(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test07(a, b, x);
		  }	  
	  }

	  @Test
	  public void Test08(){
		  methodSignature = "test08(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test08(a, b, x);
		  }
	  }

	  @Test
	  public void Test09(){
		  methodSignature = "test09(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test09(a, b, x);
		  }
	  }

	  @Test
	  public void Test10(){
		  methodSignature = "test10(sym#sym#sym)";
		  options[0] = symMethodPrefix + methodSignature;
		  String a = "aaa";
		  String b = "bbb";
		  int x = 1;
		  	
		  if(verifyNoPropertyViolation(options)){
			  ExSymExeStringsDemo.test10(a, b, x);
		  }
	  }


	 
}

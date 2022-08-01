package strings;

import gov.nasa.jpf.symbc.Debug;

public class IndexOfTest {

	public static void main(String [] args){
//		test("");
		test2("");
	}
	
	public static String test(String in){
		
		String mOut = ""; 
    	String mSearchBuffer = "";
    	String currentMatch = "";
    	int matchIndex = 0;
    	int tempIndex = 0;
    	int nextChar; 
    	int readIndex = 0;
    	
    	
    		nextChar = in.charAt(readIndex);
    		readIndex++;
    		tempIndex = mSearchBuffer.indexOf(currentMatch + (char)nextChar);
                if (tempIndex != -1) {
    			currentMatch += (char)nextChar;
    			matchIndex = tempIndex;
    		}
                
                // code to test and update mSearchBuffer
         
         return mOut;
	}
	
	public static void test2(String s) {
//		if (s.indexOf("" + s.charAt(2)) > 0) {  // constraint generation ignores charAt
//		if (s.indexOf(s + s.charAt(2)) > 0) {   // constraint generation fails with exception:
		if (s.indexOf(s.charAt(2)) > 0) { 		// constraint generation fails 
												// java.lang.ClassCastException: gov.nasa.jpf.symbc.string.SymbolicCharAtInteger cannot be cast to gov.nasa.jpf.symbc.string.StringExpression
			System.out.println("branch 1");
		} else {
			System.out.println("branch 2");
		}
	}
}

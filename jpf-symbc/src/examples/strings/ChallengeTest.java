package strings;

public class ChallengeTest {

	public static void main(String [] args){
		test("");
	}
	
	public static String test(String in){
	        String mOut = ""; 
	    	String mSearchBuffer = "";
	    	String currentMatch = "";
	    	int matchIndex = 0;
	    	int tempIndex = 0;
	    	int nextChar; 
	    	int readIndex = 0;
	    	
	    	while (readIndex < in.length()) {
	    		nextChar = in.charAt(readIndex);
	    		readIndex++;
	    		tempIndex = mSearchBuffer.indexOf(currentMatch + (char)nextChar);
	                if (tempIndex != -1) {
	    			currentMatch += (char)nextChar;
	    			matchIndex = tempIndex;
	    		}
	                
	                // code to test and update mSearchBuffer
	         }
	         return mOut;
	}
}

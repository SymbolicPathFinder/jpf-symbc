package strings;

public class StringSearch {
	public static void main (String [] args) {
		String haystack = "test: This is a tttest haystack string for testing.";	
		System.out.println(search_1("<script", haystack));
	}
	
	public static int search_1(String needle, String haystack) {
		int count = 0;
		for(int i = 0; i + needle.length() < haystack.length() + 1; i ++){
			boolean found = true;
			for(int j = 0; j < needle.length(); j++){
				found = found && (haystack.charAt(i+j) == needle.charAt(j));
			}
			if (found) count++;
		}
		return count;
	}
	
	
	public static String search_2(String c, String s){
		for(int i = 0; i < s.length(); i ++){
			if(s.substring(i,i+1).equals(c)){
				s = s.substring(0,i).concat(s.substring(i+1));			
			}
		}
		return s;
	}
	

	public static String search_3(int c, String s){
		for(int i = 0; i < s.length(); i ++){
			if(s.charAt(i) == c){
				s = s.substring(0,i).concat(s.substring(i+1));			
			}
		}
		return s;
	}
	
	public static int search_4(String needle, String haystack) {
		for(int i = 0; i < haystack.length() + 1; i ++){
			boolean found = true;
			//found = found && (haystack.substring(i,i+1).equals(needle));
			found = found && (Character.toString(haystack.charAt(i))).equals(needle);
			if (found) return i;
		}
		return -1;
	}
	
	public static int search_5(String needle, String haystack) {
		int count = 0;
		String result = "";
		int p = 0;
		for(int i = 0; i + needle.length() < haystack.length() + 1; i ++){
			if(haystack.substring(i,i+needle.length()).equals(needle)){
				count++;
				result = result + haystack.substring(p,i);
				p = i + needle.length();
			}
		}
		result = result + haystack.substring(p);
		System.out.println(result);
		return count;
	}
	
	
	
}


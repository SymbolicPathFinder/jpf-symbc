package strings;

public class PassCheck {
	
	private static String password = "Pa$$w0rd";
	
	public static void main (String [] args) {
		String p = "Pa$$w0rd";
		if(passCheckInsecure(p))
			System.out.println("Insecure Success.");
		else
			System.out.println("Insecure Fail.");
		
		
		if(passCheckSecure(p))
			System.out.println("Secure Success.");
		else
			System.out.println("Secure Fail.");
		
		
		
	}
	
	private static boolean passCheckInsecure(String p){
		int i;
		if(p.length() != password.length()) return false;
		for(i = 0; i < p.length(); i++){
			if(p.charAt(i) != password.charAt(i)){
				return false;
			}
		}
		return true;
	}

	private static boolean passCheckSecure(String p){
		boolean matched = true;
		for(int i = 0; i < p.length(); i++){
			//if(p.charAt(i) != password.charAt(i)){
			//	matched = false;
			//}
			matched = matched && p.charAt(i) != password.charAt(i);
		}
		return matched;
	}

	
	
}

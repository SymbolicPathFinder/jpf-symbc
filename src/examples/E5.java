
public class E5 {

	public static void main(String[] args) {
		String r1 = "A";
		String r2 = "BA";
		String r5 = "aa";
		strEx(r1,r2);
		strEx1(r1,r2);
		strEx2(r5);
		strEx3(r5);
		strEx4(r5);
		strEx6(r5);
		strEx7(r5);
		strEx8(r5);
	}
	
	public static void strEx (String r1, String r2) {
		String r3 = r2.concat(r1);
		//if (r2.concat(r1).contains("BAA")) {
			
		if (r3.contains("BAA")) {	
			// true branch 
			System.out.println("r3 contains BAA");
		} else {
			// false branch
			System.out.println("r3 does not contain BAA");
		}
	}
	
	
	public static void strEx1 (String r1, String r2) {
		String r3 = r2.concat(r1);
		//if (r2.concat(r1).contains("BAA")) {
			
		if (r3.contains("BAA")) {	
			// true branch 
			System.out.println("r3 contains BAA");
			if (r3.equals("BAA")) {
				System.out.println("r3 equals BAA");
			} else {
				System.out.println("r3 contains but does not equal BAA");
			}
		} else {
			// false branch
			System.out.println("r3 does not contain BAA");
		}
	}
	
	
	
	
	
	
	
	public static void strEx2 (String r5) {
		if (r5.toUpperCase().concat(r5).contains("AAaa")) {
			// true branch 
		} else {
			// false branch
		}
	}
	
	public static void strEx3 (String r5) {
		if (r5.trim().concat(r5).contains("AAaa")) {
			// true branch 
		} else {
			// false branch
		}
	}
	
	public static void strEx4 (String r5) {
		r5 = r5.concat(r5);
		if (r5.contains("AAaa")) {
			// true branch 
		} else {
			// false branch
		}
	}
	
	public static void strEx6 (String r5) {
		if (r5.contains("aa")) {
			if (r5.toUpperCase().concat(r5).contains("AAaa")) {
			// true branch 
		} else {
			// false branch
		}
		}

	}
	
	public static void strEx7 (String r5) {
		if (r5.contains("aa")) {
			if (r5.concat(r5).toUpperCase().contains("AAAA")) {
			// true branch 
		} else {
			// false branch
		}
		}

	}
	
	public static void strEx8 (String r5) {
		if (r5.trim().concat(r5).toUpperCase().contains("AA")) {
			// true branch 
		} else {
			// false branch
		}
	}
	
	
}

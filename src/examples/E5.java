import java.nio.charset.StandardCharsets;

public class E5 {

	public static void main(String[] args) {
		String r1 = "A";
		String r2 = "BA";
		String r5 = "aa";
		String r = "abc";
		testTrim(" 123abc ");
		strEx(r1,r2);
		strEx1(r1,r2);
		strEx2(r5);
		strEx3(r5);
		strEx4(r5);
		strEx6(r5);
		strEx7(r5);
		strEx8(r5);
		testStarsEndsWith(r2);
		testIndexOf(r5);
		testLength(r5);
		testReplace(r5);
		testCharAt(r5);
		testCompareTo(r5);
		//testJoin(r1,r2);
		testIsEmpty(r5);
		testStringBuilder(r);
		testSplit("aa bb");
		testEqualsIgnoreCase("AA");
		testToLowerCase("AA");
		testFormat("114514");
		testGetBytes("abc");
		testGetChars("abc");
		testLastIndexOf("ccba");
		testIntern(r);
		testValueOfInt(114514);
		testValueOfChar('a');
		testToCharArray("abc");
		//testEmptyCharAt(0);
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

	public static void testStarsEndsWith (String r5) {
		r5.startsWith("a");
		r5.endsWith("A");
	}

	public static void testIndexOf (String r5) {
		//r5.indexOf("A",1);
		if(r5.indexOf("a") > 1){
			//
		}else{
			//
		}
	}

	public static void testLength (String r5) {
		if(r5.length()>20){
			//
		} else {
			//
		}
	}

	public static void testReplace (String r5) {
		String r6 = r5.replace('a', 'c');
		//String r6 = r5.replaceAll("a", "c");
		if(r6.equals("cc")){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testCharAt (String r5) {
		char ch = r5.charAt(1);
		if(ch == 'a'){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testEmptyCharAt (int idx) {
		try{
			char ch = "".charAt(idx);
			if(ch == 'a'){
				// true branch
			}else{
				// false branch
			}
		}
		catch (StringIndexOutOfBoundsException i){
			// Exception branch
		}
	}

	public static void testCompareTo (String r5){
		if(r5.compareTo("aa")==0){
			// true branch
		}else{
			//false branch
		}
	}

	public static void testJoin (String r1, String r2) {
		if(r1 == null || r2 == null){
			return;
		}
		String r3 = String.join("", r1, r2);
		if (r3.equals("ABA")) {
			// true branch
		} else {
			// false branch
		}
	}

	public static void testIsEmpty (String r5) {
		if (r5.isEmpty()) {
			// true branch
		} else {
			// false branch
		}
	}

	public static void testStringBuilder (String r) {
		StringBuilder str = new StringBuilder(r);
		String res = str.replace(0,2,"ba").toString();
		if (res.equals("bac")) {
			// true branch
		} else {
			// false branch
		}
	}

	public static void testSplit (String r){
		String[] arr = r.split("\\s", 0);
		if(arr[0].equals("aa")){
			// true branch
		}else{
			//false
		}
	}

	public static void testEqualsIgnoreCase (String r){
		if(r.equalsIgnoreCase("AA")){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testToLowerCase (String r) {
		if (r.toLowerCase().concat(r).contains("aaAA")) {
			// true branch
		} else {
			// false branch
		}
	}

	public static void testFormat (String n) {
		String r2 = String.format("Senpai said: %s", n);
		if(r2.equals("Senpai said: 114514")){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testGetBytes (String r) {
		byte[] barr = r.getBytes();
		if(barr[0] == 0x61){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testGetChars (String r) {
		char[] arr = new char[3];
		r.getChars(0, 3, arr, 0);
		if(arr[0] == 0x61){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testLastIndexOf (String r) {
		if(r.lastIndexOf('a') > 2){
			// true branch
		}else{
			//false branch
		}
	}

	public static void testIntern (String r) {
		String r2 = r.intern();
		if(r == r2){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testValueOfChar (char c) {
		String r = String.valueOf(c);
		if (r.equals("a")){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testValueOfInt (int n) {
		String r = String.valueOf(n);
		if (r.equals("114514")){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testToCharArray (String r) {
		char[] ch = r.toCharArray();
		if(ch[0] == 0x61){
			// true branch
		}else{
			// false branch
		}
	}

	public static void testTrim(String str){
		if(str.startsWith(" ") && str.trim().equals("123abc")){
			// true branch
		}else{
			// false (error) branch
		}
	}

}

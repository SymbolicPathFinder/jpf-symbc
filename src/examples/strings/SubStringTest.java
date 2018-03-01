package strings;

public class SubStringTest {

	public static void main(String [] args){
		String s1 = "one two three";
		String s2;
		s2 = substr(s1, 4, 7);
		System.out.println(s2);
	}
	
	public static String substr(String s, int i, int j){
		if(!s.substring(i,j).equals("two")){
		//if(s.equals("two")){
			return s.substring(i,j);
		}
		else
			return "2";
	}
}

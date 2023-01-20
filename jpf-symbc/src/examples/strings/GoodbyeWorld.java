package strings;

public class GoodbyeWorld {
	public static void main (String [] args) {
		hello("input string");
	}
	
	public static void hello(String var_1) {
		int i = 0;
		if (var_1.charAt(1) == 'H'){
			i = var_1.indexOf('W');
		}
		else if (var_1.equals("Goodbye, World!")) {
			System.out.println(var_1);
		}
	}
}

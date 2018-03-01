import gov.nasa.jpf.symbc.Debug;

public class SimpleStringTest {

	public static void main(String[] args) {
		int SIZE=5;
		char[] in = new char[SIZE];
		for (int i=0;i<SIZE;i++)
			in[i]=Debug.makeSymbolicChar("in"+i);
		String in_str = new String(in);
		//if(in_str.charAt(0)=='a')
		//if(in_str.startsWith("ab"))
		if(in_str.equals("ab")) 
			System.out.println("EQ");
		else
			System.out.println("NEQ");
		Debug.printPC("PC");
	}

}

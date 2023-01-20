import gov.nasa.jpf.symbc.Debug;

public class ArrayTest {

    public int foo() {
        int[] array = {1, 2, 3};
        
        int i = 1;
        
        i = Debug.addSymbolicInt(i, "sym_i");
        
        array[i] = 5;
        
        return array[i];
        
    } 
    
    public static void main(String[] args) {
        (new ArrayTest()).foo();
    }
}

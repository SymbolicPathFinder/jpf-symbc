package lazyinit.paramAndPoly;


public abstract class AbsTest {
    public int x;
    public int y;


static class Class1 extends AbsTest {
    public Class1() {
        x = 1;
        y = 0;
    }
}

static class Class2 extends AbsTest {
    public Class2() {
        x = 3;
        y = 0;
    }
}

public static int test (AbsTest t) {
        int div = 0;
        if(t==null) return 0;
        if (t.x == 1) {
        	System.out.println("return "+0);
            return 0;
            
        }
        else if (t.x == 2) {
        	System.out.println("return "+1);
            return 1;
        } else {
        	System.out.println("return div");
            return 1/div;
        }
    }
public static void main(String[] args) {
    Class1 a = new Class1();
    int i = test(a);

    System.out.println(i);

    //Class2 b = new Class2();
    //int j = test(b);

    //System.out.println(j);
}
}
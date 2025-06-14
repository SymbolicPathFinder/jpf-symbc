public class UnsatExample {

    public static void test(int x) {
        if (x > 5 && x < 3) {
            System.out.println("UNSAT Path");
        }
    }

    public static void main(String[] args) {
        test(0);
    }
}
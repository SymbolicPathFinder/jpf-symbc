package arrays;

public class Arrays {
    public static int counter(int i, int[] arr) {
        arr[1] = i;
        arr[2] = i;
        int a = arr[1];
        int b = 1/(1+a);
        return a;
    }

    public static int counter_bis(int i, int[] arr) {
        int a = arr[i];
        return 1/(a+1);
    }
    
    public static int check_length(int i, int[] arr) {
        int j = arr.length;
        int a = arr[1];
        int b = 10/j;
        return b;
    }

    public static int[] create_array(int i) {
        return new int[i];
    }

    public static void obj_array(int i, ObjTest[] arr) {
        int a = 1/(arr[i].y + 1);
    }

    public static void check_obj_length(int i, ObjTest[] arr) {
        int j = arr.length;
        int b = 10/(i-j);
    }

    public static void obj_store(ObjTest i, ObjTest[] arr) {
        arr[1] = i;
        int a = 1/ arr[1].x;
    }        

    public static void main(String[] args) {
        int[] test = new int[30];
        ObjTest[] objTest = {new ObjTest(1,2), new ObjTest(1,0)};
        obj_array(0, objTest);
//        check_obj_length(0, objTest);
//        obj_store(new ObjTest(1,2), objTest);
        int j = counter_bis(1, test);
        int k = counter(1, test);
        int b = check_length(2, test);
        create_array(1);
    }


    public static class ObjTest {
        int x;
        int y;

        public ObjTest(int x, int y) {
            this.x = x;
            this.y = y;
        }
    }

    
}

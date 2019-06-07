package veritesting;

import veritesting.Outputs;
import veritesting.TestRegionBaseClass;
import veritesting.TestVeritesting;

import java.util.ArrayList;

public class CGTest extends TestRegionBaseClass {
    public static char[] buffer = new char[81];

    public Outputs cgtest(char ch) {
        char[] tokens = get_token(ch);
        Outputs o = new Outputs();
        o.intOutputs = new int[2];
        o.intOutputs[0] = (int) tokens[0];
        o.intOutputs[1] = isLParen(tokens[0]);
        return o;
    }

    public int isLParen(char c) {
        return c == '{' ? 1 : 0;
    }

    public char[] get_token(char ch) {
        int id = 0, i =0;

        if(ch == '"'){
            id = 1;
        }
        else if(ch == 59){
            id = 2;
        }
        ArrayList<Integer> path = new ArrayList<>();
        int s = 0;
        while (s != 100) {
            path.add(s);
            s += 1;
        }
        if (id == 1) buffer[0] = '{';
        else if (id == 2) buffer[0] = '}';
        return buffer;
    }



    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        CGTest s = new CGTest();
        t.runTest(s);
    }

    @Override
    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                         boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5,
                         char c0, char c1, char c2, char c3, char c4, char c5) {
        return cgtest(c0);
    }
}
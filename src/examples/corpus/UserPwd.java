package corpus;

/**
 * @author Kasper Luckow
 */
import java.io.InputStream;
import java.io.PrintStream;
import java.util.Scanner;

public class UserPwd {
    public static void main(String[] args) {
        Scanner scn = new Scanner(System.in);
        String pwd = scn.nextLine();
        String secret = "secret";
        if (pwd.length() != secret.length()) {
            return;
        }
        for (int i = 0; i < secret.length(); ++i) {
            if (pwd.charAt(i) == secret.charAt(i)) continue;
            double d = 1212.0;
            double d2 = 54635.3;
            double d3 = 0.0;
            for (int j = 0; j < pwd.charAt(i) * 1000000; ++j) {
                d3+=d * d2;
            }
            System.out.println(d3);
        }
    }
}

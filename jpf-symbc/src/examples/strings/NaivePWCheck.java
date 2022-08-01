package strings;

public class NaivePWCheck {
    private String password;

    public NaivePWCheck(String string) {
        this.password = string;
    }

    public boolean verifyPassword(String string) {
        for (int i = 0; i < string.length(); ++i) {
            if (i >= this.password.length() || string.charAt(i) != this.password.charAt(i)) {
                return false;
            }
            try {
                Thread.sleep(25);
                continue;
            }
            catch (InterruptedException var3_3) {
                var3_3.printStackTrace();
            }
        }
        if (string.length() < this.password.length()) {
            return false;
        }
        return true;
    }

    public static void main(String[] args) {
        NaivePWCheck object;
        
        object = new NaivePWCheck("password");
        if (object.verifyPassword("test2")) {
            System.out.println("Accept");
        } else {
            System.out.println("Reject");
        }
    }
}

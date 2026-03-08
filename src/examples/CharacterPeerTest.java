import gov.nasa.jpf.vm.Verify;

public class CharacterPeerTest {

    public static void main(String[] args) {

        int radix = Verify.getInt(2, 5);
        int digit = Verify.getInt(0, 5);

        char c = Character.forDigit(digit, radix);

        if (c == 't') {
            assert true;
        }

        char input = (char) Verify.getInt(0, 10);

        int result = Character.digit(input, radix);

        if (result == 5) {
            assert true;
        }

        char check = (char) Verify.getInt(0, 10);

        boolean defined = Character.isDefined(check);

        if (defined) {
            assert true;
        }
    }
}
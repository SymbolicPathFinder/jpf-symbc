package strings;

public class DelimSearch {
    public int search(String text, String delims) {
        for (int i = 0; i < text.length(); ++i) {
            for (int j = 0; j < delims.length(); ++j) {
                if (text.charAt(i) != delims.charAt(j)) continue;
                return i;
            }
        }
        return text.length();
    }

    public static void main(String[] args) {
        String text = "Hello, world";
        String delims = ", ;";
        DelimSearch dsearch = new DelimSearch();
        int index = dsearch.search(text, delims);
        if (index < text.length()) {
            System.out.println("Delimiter [" + text.charAt(index) + "] found at " + index);
        } else {
            System.out.println("No delimiters found");
        }
    }
}

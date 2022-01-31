/*
 * This Java source file was generated by the Gradle 'init' task.
 */
package jpf.symbc.app;

import jpf.symbc.list.LinkedList;

import static jpf.symbc.utilities.StringUtils.join;
import static jpf.symbc.utilities.StringUtils.split;
import static jpf.symbc.app.MessageUtils.getMessage;

import org.apache.commons.text.WordUtils;

public class App {
    public static void main(String[] args) {
        LinkedList tokens;
        tokens = split(getMessage());
        String result = join(tokens);
        System.out.println(WordUtils.capitalize(result));
    }
}
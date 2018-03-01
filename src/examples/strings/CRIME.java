package strings;

import java.nio.file.*;
import java.util.*;
import java.io.*;
import javax.crypto.spec.*;
import javax.crypto.*;
import java.security.*;
import java.security.spec.*;

public class CRIME
{
    private static final String IV = "AAAAAAAAAAAAAAAA";
    private static final String HELP = "CRIME send <filename> <comment>\n";
    
    public static void send(final String filename, final FileOutputStream fos, final Cipher c, final String comment) {
        final CipherOutputStream cos = new CipherOutputStream((OutputStream)fos, c);
        final byte[] commentBytes = comment.getBytes();
        try {
            final byte[] bytes = Files.readAllBytes(Paths.get(filename, new String[0]));
            final byte[] all = Arrays.copyOf(bytes, bytes.length + commentBytes.length);
            System.arraycopy((Object)commentBytes, 0, (Object)all, bytes.length, commentBytes.length);
            final byte[] compressed = LZ77T.compress(all);
            cos.write(compressed);
        }
        catch (IOException e) {
            throw new RuntimeException((Throwable)e);
        }
    }
    
    public static void main(final String[] args) throws Exception {
        if (args.length == 3 && args[0].equals("send")) {
            final Cipher cipher = Cipher.getInstance("AES/CTR/NoPadding");
            cipher.init(1, (Key)getSecretKey(), (AlgorithmParameterSpec)new IvParameterSpec("AAAAAAAAAAAAAAAA".getBytes("UTF-8")));
            try (final FileOutputStream fos = new FileOutputStream(args[1] + ".enc")) {
                send(args[1], fos, cipher, args[2]);
            }
        }
        else {
            System.out.print("CRIME send <filename> <comment>\n");
        }
    }
    
    private static SecretKey getSecretKey() throws NoSuchAlgorithmException, InvalidKeySpecException {
        final KeyGenerator aes = KeyGenerator.getInstance("AES");
        aes.init(128);
        return aes.generateKey();
    }
}

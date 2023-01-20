import java.awt.image.BufferedImage;
import java.awt.image.DataBufferByte;
import java.awt.image.Raster;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.ByteBuffer;

import gov.nasa.jpf.symbc.Debug;

public class ImageReading {

    public void foo(String fileName) {
//        System.out.println("input string: " + fileName);
//        String processedFileName = fileName.substring(0, fileName.length() - 4) + "-processed.txt";
//
//
//        BufferedImage img = null;
//        try {
//            BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(processedFileName), "UTF-8"));
//            String line;
//
//            // Get image info data (first three lines).
//            line = br.readLine();
//            int height = Integer.valueOf(line);
//            line = br.readLine();
//            int width = Integer.valueOf(line);
//            line = br.readLine();
//            int imageType = Integer.valueOf(line);
//
//            // Create BufferedImage object.
//            img = new BufferedImage(width, height, imageType);
//
//            // Get RGB data.
//            int x = 0;
//            int y = 0;
////            while ((line = br.readLine()) != null) {
////                String[] splitted = line.split(",");
////                for (String value : splitted) {
//////                    img.setConcolicRGB(x, y, Integer.valueOf(value));
////                    img.setRGB(x, y, Integer.valueOf(value));
////                    x++;
////                }
////                y++;
////                x = 0;
////            }
//            br.close();
//
//        } catch (IOException e) {
//            e.printStackTrace();
//        }
//        
//        System.out.println(img);
//
//        // Introduce symbolic variables.
//        // for (int x=0; x<img.getWidth(); x++) {
//        // for (int y=0; y<img.getHeight(); y++) {
//        // img.setRGB(x, y, Debug.addSymbolicInt(img.getRGB(x, y), "sym_" + x + "_" +
//        // y));
//        // }
//        // }
//        //
//        // } catch (FileNotFoundException e) {
//        // e.printStackTrace();
//        // } catch (IOException e1) {
//        // e1.printStackTrace();
//        // }
        
        System.out.println("Loading image: " + fileName);

        // image size
        int X = 529;
        int Y = 453;
        int imageType = 5;

        BufferedImage bi = new BufferedImage(X, Y, imageType);

        try (FileInputStream fis = new FileInputStream(fileName)) {

            byte[] bytes = new byte[Integer.BYTES];
            int x = 0;
            int y = 0;
            
            while ( (fis.read(bytes) != -1) && (x*y < X*Y) )  {
                int pixel = ByteBuffer.wrap(bytes).getInt();
                bi.setRGB(x, y, pixel);

                if (x<X-1) {
                    x++;
                } else {
                    x=0;
                    y++;
                }
            }
            
            System.out.println(x);
            System.out.println(y);
            System.out.println(bi);
            
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    public static void main(String[] args) {
        (new ImageReading()).foo(
                "/Users/yannic/Desktop/kelinci/01_engagement1_image_processor/kelinci_analysis/out_dir_48hours/queue/id_000011_orig_redpic-4-byte.jpg");
    }

}

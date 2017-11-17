package core;

import java.io.*;

/**
 * Created by Vasiliy on 2017-10-13.
 */
public class IOHelper { // TODO: review
    public static String readAllText(String filename) {
        StringBuilder sb = new StringBuilder(2048);
        try {
            FileInputStream is = new FileInputStream(filename);
            Reader r = new InputStreamReader(is, "UTF-8");
            int c = 0;
            while ((c = r.read()) != -1) {
                sb.append((char) c);
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return sb.toString();
    }

    public static void writeAllText(String filename, String text) {
        try(  PrintWriter out = new PrintWriter( new FileWriter(filename, false) )  ){
            out.println( text );
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}

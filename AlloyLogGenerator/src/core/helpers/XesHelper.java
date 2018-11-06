package core.helpers;

import org.deckfour.xes.model.XAttribute;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;
import org.deckfour.xes.out.XesXmlSerializer;

import java.io.FileOutputStream;
import java.lang.reflect.Field;

/**
 * Created by Vasiliy on 2018-02-12.
 */
public class XesHelper {
    public static String getAttributeValue(XAttribute xAttribute) throws NoSuchFieldException, IllegalAccessException {
        Field valueField = XAttributeLiteralImpl.class.getDeclaredField("value");
        valueField.setAccessible(true);
        return valueField.get(xAttribute).toString();
    }

    public static void saveLog(XLog log, String outFilename) {
        FileOutputStream fileOS = null;
        try {
            fileOS = new FileOutputStream(outFilename + log.size() + ".xes");
            new XesXmlSerializer().serialize(log, fileOS);
            fileOS.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}

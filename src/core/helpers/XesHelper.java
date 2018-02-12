package core.helpers;

import org.deckfour.xes.model.XAttribute;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;

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

}

import org.deckfour.xes.model.XAttribute;
import org.deckfour.xes.model.impl.XAttributeContinuousImpl;
import org.deckfour.xes.model.impl.XAttributeDiscreteImpl;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;

public class TestHelper {
    public static String getAttributeValueAsString(XAttribute xAttribute) {
        if (xAttribute instanceof XAttributeLiteralImpl)
            return ((XAttributeLiteralImpl) xAttribute).getValue();
        if (xAttribute instanceof XAttributeContinuousImpl)
            return String.valueOf(((XAttributeContinuousImpl) xAttribute).getValue());
        if (xAttribute instanceof XAttributeDiscreteImpl)
            return String.valueOf(((XAttributeDiscreteImpl) xAttribute).getValue());
        throw new AssertionError("Unknown type of attribute");
    }
}

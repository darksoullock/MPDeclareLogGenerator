package parsing;

import core.alloy.codegen.DeclareParser;
import org.apache.commons.lang3.StringUtils;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.Map;

/**
 * Created by Vasiliy on 2017-11-20.
 */
public class EncodeNamesTest {
    @Test
    public void testEncoding() {
        DeclareParser parser = new DeclareParser(1);
        String declare = "activity microscopisch onderzoek - gekleurd en on\n" +
                "activity sinus\n" +
                "activity inwend.geneesk.  korte kaart kosten-out\n" +
                "activity vitamine b1 - thiamine\n" +
                "activity bloedstollingsfactor xi - activiteit\n" +
                "activity immunofixatie\n" +
                "\n" +
                "activity bacteriologisc_ onderzoek_met_kweek__nie\n" +
                "activity cytologisch_onderzoek__ectocervix__\n" +
                "\n" +
                "\n" +
                "Producer code: SIOG, SGAL, SGNA, CRLA, CHE2\n" +
                "org::group: Medical_Microbiology, Pathology, General_Lab_Clinical_Chemistry, Obstetrics & Gynaecology clinic\n" +
                "SpecialismCode: 86, 7, 61, 62\n" +
                "Diagnosis_code: 106, M13\n" +
                "Section: Section_4, Section_2\n" +
                "\n" +
                "bind administratief_tarief___eerste_pol: Producer code, Diagnosis_code\n" +
                "bind bacteriologisc_ onderzoek_met_kweek__nie: org::group\n" +
                "bind cytologisch_onderzoek__ectocervix__: org::group\n" +
                "bind histologisch_onderzoek___biopten_nno: org::group\n" +
                "bind aanname_laboratoriumonderzoek: org::group, SpecialismCode, Section\n" +
                "\n" +
                "Response[aanname_laboratoriumonderzoek, ordertarief]\n" +
                "RespondedExistence[administratief_tarief___eerste_pol, aanname_laboratoriumonderzoek]\n" +
                "NotResponse[aanname_laboratoriumonderzoek, vervolgconsult_poliklinisch]\n" +
                "AlternatePrecedence[vervolgconsult_poliklinisch, administratief_tarief___eerste_pol]\n" +
                "RespondedExistence[vervolgconsult_poliklinisch, administratief_tarief___eerste_pol]\n" +
                "\n" +
                "Response[administratief_tarief___eerste_pol A, albumine T]|( A.Producer code is SIOG ) or ( A.Diagnosis_code is 106 )| \n" +
                "Absence[bacteriologisc_ onderzoek_met_kweek__nie A]|(A.org::group is not Medical_Microbiology)\n" +
                "Absence[cytologisch_onderzoek__ectocervix__ A]|(A.org::group is not Pathology)\n" +
                "Absence[histologisch_onderzoek___biopten_nno A]|(A.org::group is not Pathology)\n" +
                "NotRespondedExistence[telefonisch_consult A, alkalische_fosfatase__kinetisch_ T]|((A.Producer code is SGAL ) or ( A.Producer code is SGNA ))| \n" +
                "Absence[aanname_laboratoriumonderzoek A]|(A.Section is Section_4 ) and (A.SpecialismCode is 86) and (A.org::group is not General_Lab_Clinical_Chemistry)\n";

        String encoded = parser.encodeNames(declare);
        Map<String, String> encoding = parser.getNamesEncoding();
        String[] keys = new String[encoding.size()];
        String[] values = new String[encoding.size()];
        int i = 0;
        for (String key : encoding.keySet()) {
            keys[i] = key;
            values[i] = encoding.get(key);
            ++i;
        }

        String decoded = StringUtils.replaceEach(encoded, keys, values);
        Assert.assertEquals(declare.replace("::",":"), decoded);
    }
}

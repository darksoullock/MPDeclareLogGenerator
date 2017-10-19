package core;

import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.codegen.fnparser.DataFunction;
import core.alloy.integration.AlloyComponent;
import core.models.Expr;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.time.LocalDate;
import java.util.HashMap;
import java.util.Map;

import static core.IOHelper.readAllText;

public class Evaluator {

    public static void main(String[] args) throws Exception {
        long start = System.nanoTime();

        new DataFunction().parse("(different TransportType and (B.TransportType is not Car or A.Price<=2) and A.TransportType in (Car, Plane,Train))");

        int l = 20;
        int minl = 10;
        int ntrace = 30;

        System.out.println("Maximum no of traces: " + ntrace);

        int bitwidth = (int) Math.ceil(Math.log((double) l) / Math.log(2.0D));
        String declare = GetDeclare();
        AlloyCodeGenerator gen = new AlloyCodeGenerator(l, minl, bitwidth);
        gen.Run(declare);
        String alloyCode = gen.getAlloyCode();

        String alsFilename = "./data/temp.als";

        IOHelper.writeAllText(alsFilename, alloyCode);

        String outFilename = "./data/" + LocalDate.now() + "-L" + l + "-T";
        if (args.length > 0) {
            alsFilename = args[0];
        }

        AlloyComponent alloy = new AlloyComponent();
//        Module world = alloy.parse(alsFilename);
//        A4Solution solution = alloy.executeFromFile(l, bitwidth);
//
//        System.out.println("Found Solution: " + (solution != null && solution.satisfiable()));
//
//        AlloyXESSerializer serializer = new AlloyXESSerializer(world, getMapping(), gen.getTraceAttr());
//        serializer.serialize(solution, ntrace, outFilename, l);

        long end = System.nanoTime();
        System.out.println((end - start) / 1_000_000);
    }

    private static String GetDeclare() throws FileNotFoundException {
        return IOHelper.readAllText(new FileInputStream("./data/example.decl"));
    }

    public static Map<String, Expr> getMapping() throws FileNotFoundException { // TODO review
        Map<String, Expr> result = new HashMap<>();
        File file = new File("./data/dataout.txt");
        if (!file.exists())
            return result;
        String text = readAllText(new FileInputStream(file));
        for (String line : text.split("\n")) {
            String[] a = line.split(" ");
            Expr t = new Expr(a[1], Integer.parseInt(a[2]), Integer.parseInt(a[3]));
            result.put(a[0], t);
        }
        return result;
    }
}

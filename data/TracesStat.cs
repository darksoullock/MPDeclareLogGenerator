using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;

namespace TracesStat
{
    class Program
    {
        static void Main(string[] args)
        {
            if (args.Length == 0)
            {
                Console.WriteLine(args.Length);
                return;
            }

            var text = File.ReadAllText(args[0]);
            text = text.Replace("\n", "");
            Regex rgx = new Regex("<trace>.*?</trace>");
            Dictionary<int, int> occ = new Dictionary<int, int>();
            int totale = 0;
            int totalt = 0;
            foreach (Match m in rgx.Matches(text))
            {
                ++totalt;
                string trace = m.Value;
                int i = trace.IndexOf("lifecycle:transition", 0);
                int cnt = 0;
                while (i >= 0)
                {
                    i = trace.IndexOf("lifecycle:transition", i+1);
                    ++cnt;
                    ++totale;
                }

                if (!occ.ContainsKey(cnt))
                    occ[cnt] = 0;

                ++occ[cnt];
            }

            Console.WriteLine("L\tN");
            foreach (var i in occ.Keys.OrderBy(i=>i))
            {
                Console.WriteLine($"{i}:\t{occ[i]}");
            }
            Console.WriteLine();
            Console.WriteLine($"Traces: {totalt}\tevents: {totale}\t average length: {((double)totale)/totalt}");

            Console.ReadKey();
        }
    }
}

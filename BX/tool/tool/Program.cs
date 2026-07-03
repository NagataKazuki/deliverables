using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Net.WebSockets;

partial class Program
{
    static string RunZ3(string cnfPath)
{
    var psi = new ProcessStartInfo
    {
        FileName = "z3",
        Arguments = cnfPath,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        UseShellExecute = false,
        CreateNoWindow = true
    };

    using var p = Process.Start(psi);
    string output = p.StandardOutput.ReadToEnd();
    p.WaitForExit();
    return output;
}

    static Dictionary<int, bool> ParseModel(string text)
    {
        var model = new Dictionary<int, bool>();

        foreach (var tok in text.Split())
            if (int.TryParse(tok, out int lit))
                model[Math.Abs(lit)] = lit > 0;

        return model;
    }

    static Dictionary<string, Action<Domain, Domain, VarPool, Cnf>> Laws = new()
    {
        {"tG",LensLaws.TGet},
        {"pG",LensLaws.PGet},
        {"tP",LensLaws.TPut},
        {"pP",LensLaws.PPut},
        {"SGP",LensLaws.SGP},
        {"GP", LensLaws.GP},
        {"PG",LensLaws.PG },
        {"PP",LensLaws.PP},
        {"WPG",LensLaws.WPG },
        {"GPG",LensLaws.GPG },
        {"PGP",LensLaws.PGP },
        {"SS",LensLaws.SS },
        {"WSS", LensLaws.WSS},
        {"PS", LensLaws.PS},
        {"PI",LensLaws.PI },
        {"GS",LensLaws.GS },
        {"GI",LensLaws.GI },
        {"PT",LensLaws.PT },
        {"VD",LensLaws.VD },
        {"UD",LensLaws.UD },
        {"NotSGP",LensLaws.NotSGP},
        {"NotGP", LensLaws.NotGP},
        {"NotPG",LensLaws.NotPG },
        {"NotPP",LensLaws.NotPP},
        {"NotWPG",LensLaws.NotWPG },
        {"NotGPG",LensLaws.NotGPG },
        {"NotPGP",LensLaws.NotPGP },
        {"NotSS",LensLaws.NotSS },
        {"NotWSS", LensLaws.NotWSS},
        {"NotPS", LensLaws.NotPS},
        {"NotPI",LensLaws.NotPI },
        {"NotGS",LensLaws.NotGS },
        {"NotGI",LensLaws.NotGI },
        {"NotPT",LensLaws.NotPT },
        {"NotVD",LensLaws.NotVD },
        {"NotUD",LensLaws.NotUD },
        {"NEG", LensLaws.NEG},
        {"NEP", LensLaws.NEP},
        {"NEP2", LensLaws.NEP2 },
        {"NEP3", LensLaws.NEP3 }
    };

        static String HRocq(string[] name)
    {
        string t = $"have H{name[name.Length - 1].Replace("Not","")} : ";
        for (int i = 0; i < name.Length; ++i)
        {
            if (name[i] == "tG")
            {
                t += "GetTotal S V l";
            }
            else if (name[i] == "tP")
            {
                t += "PutTotal S V l";
            }
            else if (name[i].Contains("Not"))
            {
                t += $"{name[i].Replace("Not","")} S V l";
            }
            else
            {
                t += $"{name[i]} S V l";
            }

            if (i < name.Length - 1)
            {
                t += " -> ";
            }
        }
        return t;
    }

    static void srint(Domain S, Domain V, VarPool vars, Dictionary<int, bool> model,string[] name)
    {
    String SType = "Dom4";
    String VType = "Dom4"; 
    var t = new String[S.Size];
    var w = new String[V.Size];
    if(S.Size == 2)
    {
        SType = "bool";
        t[0] = "false";
        t[1] = "true";
    }
    if(S.Size == 3)
    {
        SType = "Dom3";
        t[0] = "a";
        t[1] = "b";
        t[2] = "c";
    }

    if(V.Size == 2)
    {
        VType = "bool";
        w[0] = "true";
        w[1] = "false";
    }

    if(V.Size == 3)
    {
        VType = "Dom3";
        w[0] = "a";
        w[1] = "b";
        w[2] = "c";
    }
    String Rocqlens = $"set (S := {SType} ); set (V := {VType} ); set (l := @mkLens {SType} {VType} ";
    Rocqlens += " (fun b => match b with";
    for (int s = 0; s < S.Size; s++)
    {
        bool found = false;
        for (int v = 0; v < V.Size; v++)
        {
            if (model.TryGetValue(vars.Get(new GKey(s, v)), out var b) && b)
            {
                Rocqlens += $"|{t[s]} => Some {w[v]}";
                found = true;
                break;
            }
        }

        if (!found)
        {
            Rocqlens += $"|{t[s]} => None";
        }
    }
    Rocqlens += " end) (fun sv => match sv with";

    for (int s = 0; s < S.Size; s++)
        for (int v = 0; v < V.Size; v++)
        {
            bool found = false;
            for (int s2 = 0; s2 < S.Size; s2++)
            {
                if (model.TryGetValue(vars.Get(new PKey(s, v, s2)), out var b) && b)
                {
                    Rocqlens += $"|({t[s]},{w[v]}) => Some {t[s2]}";
                    found = true;
                    break;
                }
            }
            if (!found)
            {
                Rocqlens += $"|({t[s]},{w[v]}) => None";
            }
        }
        Rocqlens += " end))";
        Console.WriteLine(Rocqlens);
    }

    static void Main(string[] args)
    {
        var Lens = new List<Action<Domain, Domain, VarPool, Cnf>>();
        string[] input = args.Length > 0 ? args[0].Split(' ', StringSplitOptions.RemoveEmptyEntries) : new string[] {"PP"};
        foreach (var L in input) Lens.Add(Laws[L]);

        for (int n = 2; n <= 4; ++n)
        {
            for (int m = 2; m <= 4; ++m)
            {
                Console.Write($"S = {n}, V = {m} : ");

                var S = new Domain(n);
                var V = new Domain(m);
                var vars = new VarPool();
                var cnf = new Cnf();
                
                foreach (var L in Lens) L(S, V, vars, cnf);

                string cnfPath = "out.cnf";
                using (var w = new StreamWriter(cnfPath))
                {
                    w.WriteLine($"p cnf {vars.Count} {cnf.Clauses.Count}");
                    foreach (var c in cnf.Clauses)
                        w.WriteLine($"{string.Join(" ", c)} 0");
                }

                string z3out = RunZ3(cnfPath);
                if (z3out.Contains("UNSAT"))
                {

                }
                else
                {
                   var model = ParseModel(z3out);
                   srint(S, V, vars, model,input);
                   return;
                }
            }
        }
    }
}
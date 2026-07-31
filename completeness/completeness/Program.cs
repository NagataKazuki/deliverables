using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace ImplicationSolver
{
    public record Implication(long LeftMask, long RightBit);

    public class RightHandSideReport
    {
        public string RightName { get; init; } = "";
        public int RightIndex { get; init; }
        public List<string> MainLeftPremises { get; init; } = new();
        public List<string> OmittedLeftPremises { get; init; } = new();
    }

    public class HornImplicationSolver
    {
        private readonly int ruleCount;
        private readonly string[] ruleNames;
        private readonly List<Implication> implications;
        private readonly long allTrueMask;

        public HornImplicationSolver(string[] ruleNames, List<Implication> implications)
        {
            this.ruleCount = ruleNames.Length;
            this.ruleNames = ruleNames;
            this.implications = implications;
            this.allTrueMask = ruleCount == 64 ? -1L : (1L << ruleCount) - 1L;
        }

        public long ComputeClosure(long state)
        {
            long closure = state;
            while (true)
            {
                long prev = closure;
                foreach (var imp in implications)
                {
                    if ((closure & imp.LeftMask) == imp.LeftMask)
                    {
                        closure |= imp.RightBit;
                    }
                }
                if (closure == prev) break;
            }
            return closure;
        }

        public List<RightHandSideReport> GenerateReportsByRightHandSide()
        {
            var reports = new List<RightHandSideReport>();

            var closedStates = new List<long>();
            for (long state = 1; state < allTrueMask; state++)
            {
                if (ComputeClosure(state) == state)
                {
                    closedStates.Add(state);
                }
            }

            for (int i = 0; i < ruleCount; i++)
            {
                long targetBit = 1L << i;
                var validClosed = closedStates.Where(s => (s & targetBit) == 0).ToList();

                var maximalClosed = new List<long>();

                foreach (var state in validClosed)
                {
                    bool isMaximal = true;
                    foreach (var other in validClosed)
                    {
                        if (state != other && (state & other) == state)
                        {
                            isMaximal = false;
                            break;
                        }
                    }

                    if (isMaximal)
                    {
                        maximalClosed.Add(state);
                    }
                }

                var mainPremises = new HashSet<string>();
                foreach (var m in maximalClosed)
                {
                    long gen = ReduceToMinimalGenerator(m);
                    mainPremises.Add(MaskToString(gen));
                }

                var omittedPremises = new HashSet<string>();
                for (long state = 1; state < allTrueMask; state++)
                {
                    if ((state & targetBit) != 0) continue;
                    if ((ComputeClosure(state) & targetBit) == 0)
                    {
                        string str = MaskToString(state);
                        if (!mainPremises.Contains(str))
                        {
                            omittedPremises.Add(str);
                        }
                    }
                }

                reports.Add(new RightHandSideReport
                {
                    RightName = ruleNames[i],
                    RightIndex = i,
                    MainLeftPremises = mainPremises.OrderBy(s => s.Count(c => c == '+')).ThenBy(s => s).ToList(),
                    OmittedLeftPremises = omittedPremises.OrderBy(s => s.Count(c => c == '+')).ThenBy(s => s).ToList()
                });
            }

            return reports;
        }

        private long ReduceToMinimalGenerator(long state)
        {
            long generator = state;
            for (int j = 0; j < ruleCount; j++)
            {
                long bit = 1L << j;
                if ((generator & bit) != 0)
                {
                    long testState = generator ^ bit;
                    if (testState > 0 && ComputeClosure(testState) == state)
                    {
                        generator = testState;
                    }
                }
            }
            return generator;
        }

        private string MaskToString(long mask)
        {
            if (mask == 0) return "";
            var names = new List<string>();
            for (int i = 0; i < ruleCount; i++)
            {
                if ((mask & (1L << i)) != 0) names.Add(ruleNames[i]);
            }
            return string.Join(" + ", names);
        }
    }

    public class Program
    {
        public static void Main(string[] args)
        {
            try
            {
                string fileName = args.Length > 0 ? args[0] : "input.txt";

                string filePath = Path.GetFullPath(Path.Combine(AppDomain.CurrentDomain.BaseDirectory, @"..\..\..\", fileName));

                if (!File.Exists(filePath))
                {
                    filePath = Path.Combine(Directory.GetCurrentDirectory(), fileName);
                }

                if (!File.Exists(filePath))
                {
                    Console.WriteLine($"'{fileName}'が見つからない");
                    Console.WriteLine($"探したパス: {filePath}");
                    return;
                }

                string[] allLines = File.ReadAllLines(filePath);
                int lineIndex = 0;

                string? ReadNextValidLine()
                {
                    while (lineIndex < allLines.Length)
                    {
                        string line = allLines[lineIndex++].Trim();
                        if (!string.IsNullOrEmpty(line) && !line.StartsWith("//"))
                            return line;
                    }
                    return null;
                }

                string? line1 = ReadNextValidLine();
                if (line1 == null || !int.TryParse(line1, out int expectedCount) || expectedCount <= 0)
                {
                    Console.WriteLine("エラー: input.txtの1行目は規則の数");
                    return;
                }

                string? line2 = ReadNextValidLine();
                if (line2 == null) return;

                string[] ruleNames = line2.Split(' ', StringSplitOptions.RemoveEmptyEntries);

                if (ruleNames.Length != expectedCount)
                {
                    Console.WriteLine($"\n 入力エラー");
                    Console.WriteLine($"  - 1行目の入力: {expectedCount}");
                    Console.WriteLine($"  - 2行目の入力: {ruleNames.Length} ({string.Join(", ", ruleNames)})");
                    return;
                }

                var nameToBit = new Dictionary<string, long>();
                for (int i = 0; i < expectedCount; i++)
                {
                    nameToBit[ruleNames[i]] = 1L << i;
                }

                var implications = new List<Implication>();

                while (true)
                {
                    string? line = ReadNextValidLine();
                    if (line == null || line.StartsWith(">>>>>")) break;

                    string[] parts = line.Split(new[] { "->" }, StringSplitOptions.None);
                    if (parts.Length != 2) continue;

                    string leftPart = parts[0].Trim();
                    string rightPart = parts[1].Trim();

                    long leftMask = 0;
                    string[] leftTokens = leftPart.Split(' ', StringSplitOptions.RemoveEmptyEntries);
                    foreach (var token in leftTokens)
                    {
                        if (token == "+") continue;
                        if (nameToBit.TryGetValue(token, out long bit))
                        {
                            leftMask |= bit;
                        }
                        else
                        {
                            throw new ArgumentException($"左辺に未定義の規則 '{token}' ");
                        }
                    }

                    if (nameToBit.TryGetValue(rightPart, out long rightBit))
                    {
                        implications.Add(new Implication(leftMask, rightBit));
                    }
                    else
                    {
                        throw new ArgumentException($"右辺に未定義の規則 '{rightPart}'");
                    }
                }

                var solver = new HornImplicationSolver(ruleNames, implications);
                var reports = solver.GenerateReportsByRightHandSide();

                Console.WriteLine($"(ファイル: {fileName})");
                Console.WriteLine($"規則の数: {expectedCount}件 (右辺 {expectedCount} 通り)");

                foreach (var rep in reports)
                {
                    Console.WriteLine($"右辺 : [ {rep.RightName} ]");

                    if (rep.MainLeftPremises.Any())
                    {
                        Console.WriteLine("  証明すべき反例:");
                        foreach (var left in rep.MainLeftPremises)
                        {
                            Console.WriteLine($"    ・ {left} -> {rep.RightName}");
                        }
                    }
                    else
                    {
                        Console.WriteLine("  証明するべき反例なし");
                    }

                    if (rep.OmittedLeftPremises.Any())
                    {
                        Console.WriteLine("  省略された含意:");
                        foreach (var left in rep.OmittedLeftPremises)
                        {
                            Console.WriteLine($"    ・ {left} -> {rep.RightName}");
                        }
                    }
                    Console.WriteLine();
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"\nエラーが発生しました: {ex.Message}");
            }
        }
    }
}
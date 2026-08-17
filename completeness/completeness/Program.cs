using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using Microsoft.Z3;

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

        private readonly int[] initialRuleCounts;
        private readonly List<int>[] dependents;
        private readonly int[] ruleRightIndices;
        private readonly long baseClosure;

        public HornImplicationSolver(string[] ruleNames, List<Implication> implications)
        {
            this.ruleCount = ruleNames.Length;
            this.ruleNames = ruleNames;
            this.implications = implications;
            this.allTrueMask = ruleCount == 64 ? -1L : (1L << ruleCount) - 1L;

            int impCount = implications.Count;
            initialRuleCounts = new int[impCount];
            dependents = new List<int>[ruleCount];
            for (int i = 0; i < ruleCount; i++)
            {
                dependents[i] = new List<int>();
            }
            ruleRightIndices = new int[impCount];

            long initialBaseClosure = 0;

            for (int r = 0; r < impCount; r++)
            {
                var imp = implications[r];

                int count = BitOperations.PopCount((ulong)imp.LeftMask);
                initialRuleCounts[r] = count;

                if (count == 0)
                {
                    initialBaseClosure |= imp.RightBit;
                }

                for (int i = 0; i < ruleCount; i++)
                {
                    long bit = 1L << i;
                    if ((imp.LeftMask & bit) != 0)
                    {
                        dependents[i].Add(r);
                    }
                    if (imp.RightBit == bit)
                    {
                        ruleRightIndices[r] = i;
                    }
                }
            }

            this.baseClosure = SlowComputeClosure(initialBaseClosure);
        }

        private long SlowComputeClosure(long state)
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

        public long ComputeClosure(long state)
        {
            long closure = state | baseClosure;
            long queueMask = closure;
            if (queueMask == 0) return 0;

            Span<int> counts = stackalloc int[initialRuleCounts.Length];
            initialRuleCounts.AsSpan().CopyTo(counts);

            while (queueMask != 0)
            {
                long isolatedBit = queueMask & -queueMask;
                int varIndex = BitOperations.TrailingZeroCount((ulong)isolatedBit);
                queueMask &= ~isolatedBit;

                foreach (int ruleIdx in dependents[varIndex])
                {
                    counts[ruleIdx]--;
                    if (counts[ruleIdx] == 0)
                    {
                        long rightBit = 1L << ruleRightIndices[ruleIdx];
                        if ((closure & rightBit) == 0)
                        {
                            closure |= rightBit;
                            queueMask |= rightBit;
                        }
                    }
                }
            }

            return closure;
        }

        public List<RightHandSideReport> GenerateReportsByRightHandSide()
        {
            var reports = new List<RightHandSideReport>();
            var allMainPremises = new List<HashSet<string>>();
            var allOmittedPremises = new List<HashSet<string>>();

            using var ctx = new Context();
            BoolExpr[] z3Vars = new BoolExpr[ruleCount];
            for (int i = 0; i < ruleCount; i++)
            {
                z3Vars[i] = ctx.MkBoolConst(ruleNames[i]);
            }

            var globalRules = new List<BoolExpr>();
            foreach (var imp in implications)
            {
                var lefts = new List<BoolExpr>();
                for (int v = 0; v < ruleCount; v++)
                {
                    if ((imp.LeftMask & (1L << v)) != 0) lefts.Add(z3Vars[v]);
                }

                int rightIndex = BitOperations.TrailingZeroCount((ulong)imp.RightBit);

                if (lefts.Count == 0)
                {
                    globalRules.Add(z3Vars[rightIndex]);
                }
                else
                {
                    var andExpr = ctx.MkAnd(lefts.ToArray());
                    globalRules.Add(ctx.MkImplies(andExpr, z3Vars[rightIndex]));
                }
            }

            for (int i = 0; i < ruleCount; i++)
            {
                var maximalClosed = new List<long>();
                var solver = ctx.MkSolver();

                solver.Add(globalRules.ToArray());
                solver.Add(ctx.MkNot(z3Vars[i]));

                while (solver.Check() == Status.SATISFIABLE)
                {
                    var model = solver.Model;
                    long currentMask = 0;
                    for (int v = 0; v < ruleCount; v++)
                    {
                        if (model.Evaluate(z3Vars[v]).IsTrue) currentMask |= (1L << v);
                    }

                    solver.Push();

                    for (int v = 0; v < ruleCount; v++)
                    {
                        if ((currentMask & (1L << v)) != 0) solver.Add(z3Vars[v]);
                    }

                    for (int v = 0; v < ruleCount; v++)
                    {
                        if ((currentMask & (1L << v)) == 0)
                        {
                            solver.Push();
                            solver.Add(z3Vars[v]);
                            if (solver.Check() == Status.SATISFIABLE)
                            {
                                var newModel = solver.Model;
                                for (int v2 = 0; v2 < ruleCount; v2++)
                                {
                                    if (newModel.Evaluate(z3Vars[v2]).IsTrue) currentMask |= (1L << v2);
                                }
                                solver.Pop();
                                for (int v2 = 0; v2 < ruleCount; v2++)
                                {
                                    if ((currentMask & (1L << v2)) != 0) solver.Add(z3Vars[v2]);
                                }
                            }
                            else
                            {
                                solver.Pop();
                            }
                        }
                    }
                    solver.Pop();

                    maximalClosed.Add(currentMask);

                    var falses = new List<BoolExpr>();
                    for (int v = 0; v < ruleCount; v++)
                    {
                        if ((currentMask & (1L << v)) == 0) falses.Add(z3Vars[v]);
                    }

                    if (falses.Count > 0)
                    {
                        solver.Add(ctx.MkOr(falses.ToArray()));
                    }
                    else
                    {
                        break;
                    }
                }

                var mainPremises = new HashSet<string>();
                foreach (var maxState in maximalClosed)
                {
                    long gen = ReduceToMinimalGenerator(maxState);
                    mainPremises.Add(MaskToString(gen));
                }

                allMainPremises.Add(mainPremises);
                allOmittedPremises.Add(new HashSet<string>());
            }
            long[] impliedByRight = new long[ruleCount];
            for (int i = 0; i < ruleCount; i++)
            {
                impliedByRight[i] = ComputeClosure(1L << i);
            }

            for (int i = 0; i < ruleCount; i++)
            {
                var currentMain = allMainPremises[i];
                var currentOmitted = allOmittedPremises[i];
                var toRemove = new List<string>();

                foreach (var premise in currentMain)
                {
                    for (int j = 0; j < ruleCount; j++)
                    {
                        if (i == j) continue;

                        bool implies = (impliedByRight[i] & (1L << j)) != 0;
                        if (implies)
                        {
                            if (allMainPremises[j].Contains(premise))
                            {
                                bool impliedBack = (impliedByRight[j] & (1L << i)) != 0;
                                if (impliedBack && i < j)
                                {
                                    continue;
                                }

                                toRemove.Add(premise);
                                break;
                            }
                        }
                    }
                }

                foreach (var premise in toRemove)
                {
                    currentMain.Remove(premise);
                    currentOmitted.Add(premise);
                }
            }

            for (int i = 0; i < ruleCount; i++)
            {
                reports.Add(new RightHandSideReport
                {
                    RightName = ruleNames[i],
                    RightIndex = i,
                    MainLeftPremises = allMainPremises[i].OrderBy(s => s.Count(c => c == '+')).ThenBy(s => s).ToList(),
                    OmittedLeftPremises = allOmittedPremises[i].OrderBy(s => s.Count(c => c == '+')).ThenBy(s => s).ToList()
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

                var nameToBit = new Dictionary<string, long>();
                for (int i = 0; i < expectedCount; i++)
                {
                    nameToBit[ruleNames[i]] = 1L << i;
                }

                var implications = new List<Implication>();

                while (true)
                {
                    string? line = ReadNextValidLine();
                    if (line == null || line.Equals("end", StringComparison.OrdinalIgnoreCase)) break;

                    string[] parts = line.Split(new[] { "->" }, StringSplitOptions.None);
                    if (parts.Length != 2) continue;

                    string leftPart = parts[0].Trim();
                    string rightPart = parts[1].Trim();

                    long leftMask = 0;
                    string[] leftTokens = leftPart.Split(' ', StringSplitOptions.RemoveEmptyEntries);
                    foreach (var token in leftTokens)
                    {
                        if (token == "+") continue;
                        leftMask |= nameToBit[token];
                    }

                    implications.Add(new Implication(leftMask, nameToBit[rightPart]));
                }

                var solver = new HornImplicationSolver(ruleNames, implications);
                var reports = solver.GenerateReportsByRightHandSide();

                Console.WriteLine($"(ファイル: {fileName})");
                Console.WriteLine($"規則の数: {expectedCount}");

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
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"\nエラーが発生しました: {ex.Message}");
            }
        }
    }
}
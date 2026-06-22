using System;
using System.Collections.Generic;
using System.Linq;

sealed record Domain(int Size)
{
    public IEnumerable<int> Elems => Enumerable.Range(0, Size);
}

sealed class VarPool
{
    private int _next = 1;
    private readonly Dictionary<object, int> _map = new();

    public IEnumerable<object> Keys => _map.Keys;
    public int Get(object key)
    {
        if (!_map.TryGetValue(key, out var v))
        {
            v = _next++;
            _map[key] = v;
        }
        return v;
    }
    public int Count => _next - 1;


}

record GKey(int S, int V);
record PKey(int S, int V, int S2);
record XKey(int S, int Sp, int V);
record XXKey(int S, int Sp, int V, int Vp);
record XXXKey(int S, int Sp, int Spp, int V, int Vp);

record SKey(int S);
record VKey(int V);

record SEqKey(int S, int Sp);

sealed class Cnf
{
    public List<int[]> Clauses { get; } = new();
    public void Add(params int[] lits) => Clauses.Add(lits);
}


using System.Collections.Generic;

sealed class LensModel
{
    public Dictionary<GKey, bool> GetMap { get; } = new();

    public Dictionary<PKey, bool> PutMap { get; } = new();
}
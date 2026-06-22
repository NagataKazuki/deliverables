using System.Collections.Generic;

static class Z3ModelParser
{
    public static LensModel Parse(Domain S,Domain V,VarPool vars,Dictionary<int, bool> model)
    {
        var result = new LensModel();

        foreach (var key in vars.Keys)
        {
            int id = vars.Get(key);

            if (!model.TryGetValue(id, out bool value))
                continue;

            switch (key)
            {
                case GKey g:
                    result.GetMap[g] = value;
                    break;

                case PKey p:
                    result.PutMap[p] = value;
                    break;
            }
        }

        return result;
    }
}
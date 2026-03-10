using System;
using System.Collections.Generic;
using System.Linq;


static class LensLaws
{
    public static void TGet(Domain S, Domain V, VarPool vars, Cnf cnf) 
    { 
        foreach (var s in S.Elems) 
        {
            cnf.Add(V.Elems.Select(v => vars.Get(new GKey(s, v))).ToArray()); 
            foreach (var v1 in V.Elems) 
                foreach (var v2 in V.Elems) 
                    if (v1 < v2) 
                        cnf.Add(-vars.Get(new GKey(s, v1)), 
                        -vars.Get(new GKey(s, v2))); 
        }
    }
    public static void TPut(Domain S, Domain V, VarPool vars, Cnf cnf) 
    { 
        foreach (var s in S.Elems) 
            foreach (var v in V.Elems) 
            {
                cnf.Add(S.Elems.Select(s2 => vars.Get(new PKey(s, v, s2))).ToArray()); 
                foreach (var s1 in S.Elems) 
                    foreach (var s2 in S.Elems) 
                        if (s1 < s2) cnf.Add(-vars.Get(new PKey(s, v, s1)),
                            -vars.Get(new PKey(s, v, s2))); 
            } 
    }
    public static void PGet(Domain S, Domain V, VarPool vars, Cnf cnf) 
    { 
        foreach (var s in S.Elems)
        { 
            foreach (var v1 in V.Elems) 
                foreach (var v2 in V.Elems) 
                    if (v1 < v2) 
                        cnf.Add(-vars.Get(new GKey(s, v1)), 
                        -vars.Get(new GKey(s, v2))); 
        } 
    }
    public static void PPut(Domain S, Domain V, VarPool vars, Cnf cnf) 
    { 
        foreach (var s in S.Elems) 
            foreach (var v in V.Elems)
            { 
                foreach (var s1 in S.Elems) 
                    foreach (var s2 in S.Elems) 
                        if (s1 < s2) 
                            cnf.Add(-vars.Get(new PKey(s, v, s1)), 
                                -vars.Get(new PKey(s, v, s2)));
            } 
    }



    public static void SGP(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var s2 in S.Elems)
                foreach (var v in V.Elems)
                    cnf.Add(
                        -vars.Get(new GKey(s2, v)),
                        vars.Get(new PKey(s, v, s2))
                    );
    }

    public static void GP(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var v in V.Elems)
                cnf.Add(
                    -vars.Get(new GKey(s, v)),
                     vars.Get(new PKey(s, v, s))
                );
    }

    public static void PG(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var s2 in S.Elems)
                foreach (var v in V.Elems)
                    cnf.Add(
                        -vars.Get(new PKey(s, v, s2)),
                        vars.Get(new GKey(s2, v))
                    );
    }


    public static void PP(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var s2 in S.Elems)
                foreach (var s3 in S.Elems)
                    foreach (var v in V.Elems)
                        foreach (var v2 in V.Elems)
                            cnf.Add(
                                -vars.Get(new PKey(s, v, s2)),
                                -vars.Get(new PKey(s2, v2, s3)),
                                 vars.Get(new PKey(s, v2, s3))
                            );
    }

    public static void WPG(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var s2 in S.Elems)
                foreach (var v in V.Elems)
                    foreach (var v2 in V.Elems)
                        cnf.Add(
                            -vars.Get(new PKey(s, v, s2)),
                            -vars.Get(new GKey(s2, v2)),
                             vars.Get(new PKey(s, v2, s2))
                        );
    }

    public static void PGP(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var s2 in S.Elems)
                foreach (var v in V.Elems)
                    foreach (var v2 in V.Elems)
                        cnf.Add(
                            -vars.Get(new PKey(s, v, s2)),
                            -vars.Get(new GKey(s2, v2)),
                             vars.Get(new PKey(s2, v2, s2))
                        );
    }

    public static void GPG(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var s2 in S.Elems)
                foreach (var v in V.Elems)
                    cnf.Add(
                        -vars.Get(new GKey(s, v)),
                        -vars.Get(new PKey(s, v, s2)),
                         vars.Get(new GKey(s2, v))
                    );
    }

    public static void UD(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var s2 in S.Elems)
                foreach (var v in V.Elems)
                    foreach (var v2 in V.Elems)
                        cnf.Add(
                            -vars.Get(new PKey(s, v, s2)),
                            -vars.Get(new GKey(s, v2)),
                             vars.Get(new PKey(s2, v2, s))
                        );
    }

    public static void GI(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s1 in S.Elems)
            foreach (var s2 in S.Elems)
                if (s1 != s2)
                    foreach (var v in V.Elems)
                        cnf.Add(
                            -vars.Get(new GKey(s1, v)),
                            -vars.Get(new GKey(s2, v))
                        );
    }

    public static void GS(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var v in V.Elems)
            cnf.Add(
                S.Elems
                 .Select(s => vars.Get(new GKey(s, v)))
                 .ToArray()
            );
    }


    public static void PT(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                {
                    cnf.Add(
                        -vars.Get(new PKey(s, v, sp)),
                         vars.Get(new PKey(sp, v, sp))
                    );
                }
    }

    public static void SS(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            cnf.Add(
                V.Elems
                 .Select(v => vars.Get(new PKey(s, v, s)))
                 .ToArray()
            );
    }


    public static void WSS(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var vp in V.Elems)
                    cnf.Add(
                        V.Elems
                         .Select(v => vars.Get(new PKey(s, v, s)))
                         .Append(-vars.Get(new PKey(sp, vp, s)))
                         .ToArray()
                    );
    }


    public static void PS(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            cnf.Add(
                S.Elems
                 .SelectMany(sp => V.Elems.Select(v => vars.Get(new PKey(sp, v, s))))
                 .ToArray()
            );
    }

    public static void VD(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s1 in S.Elems)
            foreach (var s2 in S.Elems)
                foreach (var s3 in S.Elems)
                    foreach (var v1 in V.Elems)
                        foreach (var v2 in V.Elems)
                            if (v1 != v2)
                                cnf.Add(
                                    -vars.Get(new PKey(s1, v1, s3)),
                                    -vars.Get(new PKey(s2, v2, s3))
                                );
    }

    public static void PI(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        foreach (var s in S.Elems)
            foreach (var s2 in S.Elems)
                foreach (var v1 in V.Elems)
                    foreach (var v2 in V.Elems)
                        if (v1 != v2)
                            cnf.Add(
                                -vars.Get(new PKey(s, v1, s2)),
                                -vars.Get(new PKey(s, v2, s2))
                            );
    }

    public static void NotSGP(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                {
                    int x = vars.Get(new XKey(s, sp, v));
                    selectors.Add(x);

                    cnf.Add(
                        -x,
                        vars.Get(new GKey(sp, v))
                    );

                    
                    cnf.Add(
                        -x,
                        -vars.Get(new PKey(s, v, sp))
                    );
                }
        cnf.Add(selectors.ToArray());
    }

    public static void NotGP(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                {
                    int x = vars.Get(new XKey(s, sp, v));
                    selectors.Add(x);

                    cnf.Add(
                        -x,
                        vars.Get(new GKey(s, v))
                    );


                    cnf.Add(
                        -x,
                        -vars.Get(new PKey(s, v, s))
                    );
                }
        cnf.Add(selectors.ToArray());
    }


    public static void NotPG(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                {
                    int x = vars.Get(new XKey(s, sp, v));
                    selectors.Add(x);

                    cnf.Add(
                        -x,
                        vars.Get(new PKey(s, v, sp))
                    );
                    cnf.Add(
                        -x,
                        -vars.Get(new GKey(sp, v))
                    );
                }
        cnf.Add(selectors.ToArray());
    }

    public static void NotPP(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var spp in S.Elems)
                    foreach (var v in V.Elems)
                        foreach (var vp in V.Elems)
                        {
                            int x = vars.Get(new XXXKey(s, sp, spp, v, vp));
                            selectors.Add(x);

                            cnf.Add(
                                -x,
                                vars.Get(new PKey(s, v, sp))
                            );
                            cnf.Add(
                                -x,
                                vars.Get(new PKey(sp, vp, spp))
                            );
                            cnf.Add(
                                -x,
                                -vars.Get(new PKey(s, vp, spp))
                            );
                        }
        cnf.Add(selectors.ToArray());
    }


    public static void NotWPG(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                    foreach (var vp in V.Elems)
                    {
                        int x = vars.Get(new XXKey(s, sp, v, vp));
                        selectors.Add(x);
                        cnf.Add(
                            -x,
                            vars.Get(new PKey(s, v, sp))
                        );
                        cnf.Add(
                            -x,
                            vars.Get(new GKey(sp, vp))
                        );
                        cnf.Add(
                            -x,
                            -vars.Get(new PKey(s, vp, sp))
                        );
                    }
        cnf.Add(selectors.ToArray());
    }

    public static void NotPGP(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                    foreach (var vp in V.Elems)
                    {
                        int x = vars.Get(new XXKey(s, sp, v, vp));
                        selectors.Add(x);
                        cnf.Add(
                            -x,
                            vars.Get(new PKey(s, v, sp))
                        );
                        cnf.Add(
                            -x,
                            vars.Get(new GKey(sp, vp))
                        );
                        cnf.Add(
                            -x,
                            -vars.Get(new PKey(sp, vp, sp))
                        );
                    }
        cnf.Add(selectors.ToArray());
    }

    public static void NotGPG(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                {
                    int x = vars.Get(new XKey(s, sp, v));
                    selectors.Add(x);
                    cnf.Add(
                        -x,
                        vars.Get(new GKey(s, v))
                    );
                    cnf.Add(
                        -x,
                        vars.Get(new PKey(s, v, sp))
                    );
                    cnf.Add(
                        -x,
                        -vars.Get(new GKey(sp, v))
                    );
                }
        cnf.Add(selectors.ToArray());
    }

    public static void NotUD(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                    foreach (var vp in V.Elems)
                    {
                        int x = vars.Get(new XXKey(s, sp, v, vp));
                        selectors.Add(x);
                        cnf.Add(
                            -x,
                            vars.Get(new PKey(s, v, sp))
                        );
                        cnf.Add(
                            -x,
                            vars.Get(new GKey(s, vp))
                        );
                        cnf.Add(
                            -x,
                            -vars.Get(new PKey(sp, vp, s))
                        );
                    }
        cnf.Add(selectors.ToArray());
    }

    public static void NotGI(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                if (s != sp)
                    foreach (var v in V.Elems)
                    {
                        int x = vars.Get(new XKey(s, sp, v));
                        selectors.Add(x);
                        cnf.Add(
                            -x,
                            vars.Get(new GKey(s, v))
                        );
                        cnf.Add(
                            -x,
                            vars.Get(new GKey(sp, v))
                        );

                        cnf.Add(
                            -x,
                            -vars.Get(new SEqKey(s, sp))
                        );
                    }
        cnf.Add(selectors.ToArray());
    }

    public static void NotGS(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var v in V.Elems)
        {
            int x = vars.Get(new VKey(v));
            selectors.Add(x);

            foreach (var s in S.Elems)
            {
                cnf.Add(
                    -x,
                    -vars.Get(new GKey(s, v))
                );
            }
        }
        cnf.Add(selectors.ToArray());
    }


    public static void NotPT(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                {
                    int x = vars.Get(new XKey(s, sp, v));
                    selectors.Add(x);

                    cnf.Add(
                        -x,
                        vars.Get(new PKey(s, v, sp))
                    );
                    cnf.Add(
                        -x,
                        -vars.Get(new PKey(sp, v, sp))
                    );
                }
        cnf.Add(selectors.ToArray());
    }

    public static void NotSS(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
        {
            int x = vars.Get(new SKey(s));
            selectors.Add(x);

            foreach (var v in V.Elems)
            {
                cnf.Add(
                    -x,
                    -vars.Get(new PKey(s, v, s))
                );
            }
        }
        cnf.Add(selectors.ToArray());
    }


    public static void NotWSS(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var vp in V.Elems)
                {
                    int x = vars.Get(new XKey(s, sp, vp));
                    selectors.Add(x);
                    cnf.Add(
                        -x,
                        vars.Get(new PKey(sp, vp, s))
                    );
                    foreach (var v in V.Elems)
                    {
                        cnf.Add(
                            -x,
                            -vars.Get(new PKey(s, v, s))
                        );
                    }
                }
        cnf.Add(selectors.ToArray());
    }


    public static void NotPS(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
        {
            int x = vars.Get(new SKey(s));
            selectors.Add(x);
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                {
                    cnf.Add(
                        -x,
                        -vars.Get(new PKey(sp, v, s))
                    );
                }
        }
        cnf.Add(selectors.ToArray());
    }

    public static void NotVD(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var s2 in S.Elems)
                    foreach (var v in V.Elems)
                        foreach (var vp in V.Elems)
                            if (v != vp)
                            {
                                int x = vars.Get(new XXXKey(s, sp, s2, v, vp));
                                selectors.Add(x);
                                cnf.Add(
                                    -x,
                                    vars.Get(new PKey(s, v, s2))
                                );
                                cnf.Add(
                                    -x,
                                    vars.Get(new PKey(sp, vp, s2))
                                );
                            }
        cnf.Add(selectors.ToArray());
    }

    public static void NotPI(Domain S, Domain V, VarPool vars, Cnf cnf)
    {
        var selectors = new List<int>();

        foreach (var s in S.Elems)
            foreach (var sp in S.Elems)
                foreach (var v in V.Elems)
                    foreach (var vp in V.Elems)
                        if (v != vp)
                        {
                            int x = vars.Get(new XXKey(s, sp, v, vp));
                            selectors.Add(x);
                            cnf.Add(
                                -x,
                                vars.Get(new PKey(s, v, sp))
                            );
                            cnf.Add(
                                -x,
                                vars.Get(new PKey(s, vp, sp))
                            );
                        }
        cnf.Add(selectors.ToArray());
    }
}


///////////////////////////////////////////////////////////////////////////
//  Torsion growth for elliptic curves induced by Diophantine triples
///////////////////////////////////////////////////////////////////////////

SetMemoryLimit(30 * 1024^3);

// Format torsion subgroup nicely
function TorsionString(G)
    inv := AbelianInvariants(G);
    parts := [ Sprintf("Z/%o", n) : n in inv | n ne 1 ];
    if #parts eq 0 then
        return "trivial";
    end if;
    return Join(parts, " x ");
end function;

// Induced elliptic curve:
// y^2 = (x+ab)(x+ac)(x+bc)
function TripleCurveOverField(a,b,c,K)
    aa := K!a;
    bb := K!b;
    cc := K!c;

    s2 := aa*bb + aa*cc + bb*cc;
    s3 := aa*bb*cc;

    return EllipticCurve([ K | 0, s2, 0, s3*(aa+bb+cc), s3^2 ]);
end function;

// regular (Euler-type) triple: c = a+b+2r, with r^2 = ab+1
// Returns ok, a, b, c, r
function EulerTriple(a,b)
    ok, r := IsSquare(a*b + 1);
    if not ok then
        return false, _, _, _, _;
    end if;

    if r le 0 then
        return false, _, _, _, _;
    end if;

    c := a + b + 2*r;
    return true, a, b, c, r;
end function;

// Return only those quadratic fields where torsion grows
// Output: <torsion over Q, list of <d, invariants, string>>
function GrowthDataForTriple(a,b,c,Dlist)
    E := TripleCurveOverField(a,b,c,Rationals());
    GQ, _ := TorsionSubgroup(E);
    invQ := AbelianInvariants(GQ);

    growth := [* *];

    for d in Dlist do
        K<w> := QuadraticField(d);
        EK := TripleCurveOverField(a,b,c,K);
        GK, _ := TorsionSubgroup(EK);
        invK := AbelianInvariants(GK);

        if invK ne invQ then
            Append(~growth, <d, invK, TorsionString(GK)>);
        end if;
    end for;

    return TorsionString(GQ), growth;
end function;

// Print growth data for a fixed triple
procedure PrintGrowthDataForTriple(a,b,c,Dlist)
    torsQ, growth := GrowthDataForTriple(a,b,c,Dlist);

    print "Triple =", <a,b,c>;
    print "  Over Q :", torsQ;

    if #growth eq 0 then
        print "  No torsion growth in the chosen quadratic fields.";
        return;
    end if;

    for rec in growth do
        d := rec[1];
        s := rec[3];
        print Sprintf("  Over Q(sqrt(%o)) :", d), s;
    end for;
end procedure;

// Same, starting from a,b with ab+1 square
procedure PrintGrowthDataFromPair(a,b,Dlist)
    ok, aa, bb, cc, r := EulerTriple(a,b);

    if not ok then
        print "Input <", a, ",", b, "> does not satisfy ab+1 = r^2 with r > 0.";
        return;
    end if;

    print "a,b,r,c =", <aa,bb,r,cc>;
    PrintGrowthDataForTriple(aa,bb,cc,Dlist);
end procedure;

// Search all pairs 1 <= a < b <= B with ab+1 a square,
// and print only those triples with torsion growth somewhere in Dlist
procedure SearchEulerPairs(B,Dlist)
    for a in [1..B] do
        for b in [a+1..B] do
            ok, aa, bb, cc, r := EulerTriple(a,b);

            if ok then
                torsQ, growth := GrowthDataForTriple(aa,bb,cc,Dlist);

                if #growth gt 0 then
                    print "--------------------------------------------------";
                    print "a,b,r,c =", <aa,bb,r,cc>;
                    print "Over Q   =", torsQ;
                    for rec in growth do
                        print Sprintf("Q(sqrt(%o)) =", rec[1]), rec[3];
                    end for;
                end if;
            end if;
        end for;
    end for;
end procedure;

// Same search, but return the data instead of printing it
function SearchEulerPairsData(B,Dlist)
    out := [* *];

    for a in [1..B] do
        for b in [a+1..B] do
            ok, aa, bb, cc, r := EulerTriple(a,b);

            if ok then
                torsQ, growth := GrowthDataForTriple(aa,bb,cc,Dlist);

                if #growth gt 0 then
                    Append(~out, <aa,bb,cc,r,torsQ,growth>);
                end if;
            end if;
        end for;
    end for;

    return out;
end function;


procedure PrintDataByField(data)
    Dset := {};

    for item in data do
        for g in item[6] do
            Include(~Dset, g[1]);
        end for;
    end for;

    ds := Sort(Setseq(Dset));

    for d in ds do
        print "----------------------------------------";
        print Sprintf("Q(sqrt(%o))", d);

        for item in data do
            a := item[1];
            b := item[2];
            c := item[3];
            r := item[4];

            for g in item[6] do
                if g[1] eq d then
                    print Sprintf("  <%o,%o,%o>  (r=%o)  ->  %o", a, b, c, r, g[3]);
                end if;
            end for;
        end for;
    end for;
end procedure;



Dlist2 := [ d : d in [-100..100] | d ne 0 and d ne 1 and IsSquarefree(d) ];
data := SearchEulerPairsData(1000,Dlist2);
PrintDataByField(data);





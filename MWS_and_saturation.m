function GeneratorReductions(C, P0, P1, P2, q)
    Cq := ChangeRing(C, GF(q));
    Jq := Jacobian(Cq);

    P0q := Cq!P0;
    P1q := Cq!P1;
    P2q := Cq!P2;

    return Cq, Jq, P0q, P1q - P0q, P2q - P0q;
end function;

// Reduction-based ell-saturation test
//
// This is a sufficient test.  For ell odd, and for
// Gamma = <D1,D2>, Gamma is ell-saturated if no nonzero class
// a*D1+b*D2 mod ell is divisible by ell in J(Q)/torsion.
// If such a class were ell-divisible over Q, then its reduction would be
// ell-divisible in J(F_q) for every good q.
//
// At a good prime q with v_ell(#J(F_q)) = 1, an element E in J(F_q) is
// ell-divisible only if (#J(F_q)/ell)*E = 0.  Thus a nonzero value of
// (#J(F_q)/ell)*(a*D1q+b*D2q) proves that this combination is not
// ell-divisible over Q.  We search for such a q for every nonzero
// (a,b) in F_ell^2.

function EllSaturationByReductions(C, P0, P1, P2, ell, B)
    combos := [ <a,b> : a,b in [0..ell-1] | not (a eq 0 and b eq 0) ];
    remaining := { i : i in [1..#combos] };
    used_primes := [];

    for q in PrimesInInterval(5, B) do
        if q in BadReductionPrimes then
            continue;
        end if;

        if #remaining eq 0 then
            break;
        end if;

        try
            Cq, Jq, P0q, G1q, G2q := GeneratorReductions(C, P0, P1, P2, q);
            Nq := #Jq;

            if Valuation(Nq, ell) ne 1 then
                continue;
            end if;

            mult := ExactQuotient(Nq, ell);
            H1 := mult*G1q;
            H2 := mult*G2q;
            ruled_out_here := {};

            for i in remaining do
                a := combos[i][1];
                b := combos[i][2];

                if not IsZero(a*H1 + b*H2) then
                    Include(~ruled_out_here, i);
                end if;
            end for;

            if #ruled_out_here gt 0 then
                remaining diff:= ruled_out_here;
                Append(~used_primes, q);
            end if;

        catch err
            print "Skipping q =", q, "in saturation test because of error:";
            print err`Object;
        end try;
    end for;

    if #remaining eq 0 then
        print "ell =", ell, ": saturated; primes used =", used_primes;
        return true;
    end if;

    print "ell =", ell, ": inconclusive;", #remaining,
          "combination(s) remain.";
    return false;
end function;

// Coleman residue helpers
function ColemanResidueKey(P, p)
    Fp := GF(p);
    bx := < Fp!(P`b[i]) : i in [1..#P`b] >;
    return < P`inf, Fp!(P`x), bx >;
end function;

function ColemanPointToAffineCoords(P, p)
    if P`inf then
        return <0,0,0>, false;
    end if;

    Fp := GF(p);
    xbar := Fp!(P`x);
    ybar := Fp!(P`b[2]);

    return <Integers()!xbar, Integers()!ybar, 1>, true;
end function;

function ChabautyTargetResidueCoords(L, Qpoints, p)
    known_keys := { ColemanResidueKey(P, p) : P in Qpoints };
    candidate_keys := { ColemanResidueKey(P, p) : P in L };
    target_keys := candidate_keys diff known_keys;

    print "Chabauty residue disks: known =", #known_keys,
          "; MWS targets =", #target_keys;

    coords := [];
    seen := {};

    for P in L do
        key := ColemanResidueKey(P, p);

        if key in target_keys and not key in seen then
            c, ok := ColemanPointToAffineCoords(P, p);

            if ok then
                Append(~coords, c);
                Include(~seen, key);
            else
                print "MWS target residue class at infinity or non-affine:", key;
                print "This script does not convert it automatically.";
            end if;
        end if;
    end for;

    return coords, target_keys;
end function;

// Mordell-Weil sieve
function MWSieve(C, P0, P1, P2, p, target_coords, m, auxiliary_primes)
    Cp, Jp, P0p, G1p, G2p := GeneratorReductions(C, P0, P1, P2, p);
    Np := #Jp;

    print "============================================================";
    print "Mordell-Weil sieve: p =", p, ", m =", m;

    ok, multp := IsDivisibleBy(Np, m);
    if not ok then
        print "m does not divide #J(F_p); stopping.";
        return [];
    end if;
    G1p_m := multp*G1p;
    G2p_m := multp*G2p;

    allpairs := { <a,b> : a,b in [0..m-1] };

    targets := [ Cp![coords[1], coords[2], coords[3]] : coords in target_coords ];
    target_proj := [ multp*(R - P0p) : R in targets ];

    survivors := [
        { ab : ab in allpairs |
          ab[1]*G1p_m + ab[2]*G2p_m eq target_proj[i] }
        : i in [1..#targets]
    ];

    print "Number of target residue classes:", #targets;
    print "Initial survivor counts:", [ #survivors[i] : i in [1..#survivors] ];

    for q in auxiliary_primes do
        if q in BadReductionPrimes or q eq p then
            print "Skipping q =", q, "because it is bad or equal to p.";
            continue;
        end if;

        Cq, Jq, P0q, G1q, G2q := GeneratorReductions(C, P0, P1, P2, q);
        Nq := #Jq;
        d := GCD(m, Nq);

        if d eq 1 then
            print "q =", q, "has d = 1, so it gives no condition for m =", m;
            continue;
        end if;

        multq := ExactQuotient(Nq, d);
        G1q_d := multq*G1q;
        G2q_d := multq*G2q;
        Iq := { multq*(R - P0q) : R in Points(Cq) };

        old_counts := [ #survivors[i] : i in [1..#survivors] ];

        for i in [1..#targets] do
            if #survivors[i] ne 0 then
                survivors[i] := {
                    ab : ab in survivors[i] |
                    ab[1]*G1q_d + ab[2]*G2q_d in Iq
                };
            end if;
        end for;

        new_counts := [ #survivors[i] : i in [1..#survivors] ];
        print "q =", q, ", d =", d, ":", old_counts, "->", new_counts;
    end for;

    final_counts := [ #survivors[i] : i in [1..#survivors] ];
    print "Final survivor counts:", final_counts;

    if &and[ c eq 0 : c in final_counts ] then
        print "SUCCESS: all MWS target residue classes are ruled out.";
    else
        print "NOT COMPLETE: some MWS target residue classes survive.";
    end if;

    if PrintSurvivorSetsAtEnd then
        for i in [1..#survivors] do
            print "Target", i, targets[i], "survivors:", survivors[i];
        end for;
    end if;

    return survivors;
end function;
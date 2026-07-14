// Chabauty--Coleman + Mordell--Weil sieve for
// C : 4*k^3*(k+1)*s^3*(s+2) = (2*k+1)*(2*s+1)
//
// The Legendre 3-torsion criterion gives the plane curve
//
//   4*k^3*(k+1)*s^3*(s+2) = (2*k+1)*(2*s+1).
//
// To compute its rational points, we pass to a hyperelliptic model.
// The useful substitution is z = k*s.  Then s = z/k, and after clearing
// denominators the equation becomes
//
//   4*z^3*(k+1)*(z+2*k) = (2*k+1)*(2*z+k).
//
// This is quadratic in k:
//
//   (8*z^3 - 2)*k^2
// + (4*z^4 + 8*z^3 - 4*z - 1)*k
// + (4*z^4 - 2*z) = 0.
//
// Thus the projection to the z-line is a double cover.  Its branch
// polynomial is the discriminant Delta(z), so the curve is birational to
// the hyperelliptic curve w^2 = Delta(z).  The inverse formula is
//
//   k = (w - B(z))/(2*A(z)),
//
// where A(z)=8*z^3-2 and B(z)=4*z^4+8*z^3-4*z-1.

SetPath("Classical_Chabauty");
load "coleman.m";

Qz<z> := PolynomialRing(Rationals());

A := 8*z^3 - 2;
B := 4*z^4 + 8*z^3 - 4*z - 1;
C0 := 4*z^4 - 2*z;

Delta := B^2 - 4*A*C0;
Delta := Qz!Delta;

assert Delta eq
    16*z^8 - 64*z^7 + 64*z^6 - 32*z^5
    + 24*z^4 - 16*z^3 + 16*z^2 - 8*z + 1;

C := HyperellipticCurve(Delta);
J := Jacobian(C);

// One can also confirm that this hyperelliptic C is
// isomorphic over Q to the original curve:
// A2<k,s> := AffineSpace(Rationals(), 2);
// C3 := Curve(A2,  4*k^3*(k+1)*s^3*(s+2)-(2*k+1)*(2*s+1));
// PC3 := ProjectiveClosure(C3);
// IsIsomorphic(PC3, C);
// this command returns true after ~8.6 secs


// used by MWS_and_saturation.m
BadReductionPrimes := Seqset(BadPrimes(C));
PrintSurvivorSetsAtEnd := false;

load "MWS_and_saturation.m";

// Coleman equation in Q[z][w], monic in w.
Qzw<w> := PolynomialRing(Qz);
Q := w^2 - Delta;


// Basic information
print "============================================================";
print "Basic information";
print "Genus =", Genus(C);
print "Bad reduction primes =", BadReductionPrimes;
print "Discriminant factorization =",
      Factorization(Integers()!Discriminant(Delta));

PointSearchBound := 10000;
pts := Setseq(Points(C : Bound := PointSearchBound));

print "Rational points found up to height", PointSearchBound, ":", #pts;
for P in pts do
    print P;
end for;

ub := RankBound(J);
print "Rank upper bound =", ub;

// Jacobian structures at small good primes
//
// These data give a torsion bound and suggest useful sieve moduli.
// The gcd of #J(F_p) over good primes up to 100 is 16, so the rational
// torsion is 2-primary. Therefore odd moduli avoid rational torsion.
print "============================================================";
print "Jacobian structures at good primes p <= 100";

good_primes := [ p : p in PrimesInInterval(5,100) | not p in BadReductionPrimes ];

orders := [];

for p in good_primes do
    Cp := ChangeRing(C, GF(p));
    Jp := Jacobian(Cp);
    Aab, phi := AbelianGroup(Jp);

    Append(~orders, #Jp);

    print "p =", p,
          "#J(F_p) =", #Jp,
          "structure =", Invariants(Aab);
end for;

TorsionBound := GCD(orders);
print "Torsion bound from these primes:", TorsionBound;

// Find a full rank subgroup Gamma = <D1,D2>
function FindIndependentPair(pts, P0)
    candidates := [ P : P in pts | P ne P0 ];

    for i in [1..#candidates] do
        for j in [i+1..#candidates] do
            P1 := candidates[i];
            P2 := candidates[j];

            D1 := P1 - P0;
            D2 := P2 - P0;

            try
                reg := Regulator([D1,D2]);

                if Abs(reg) gt 10^(-20) then
                    return P1, P2, D1, D2, reg;
                end if;
            catch err
                dummy := 0;
            end try;
        end for;
    end for;

    error "No independent pair found among the known rational points.";
end function;

P0 := C![1,-4,0];

P1, P2, D1, D2, RegGamma :=
    FindIndependentPair(pts, P0);

print "============================================================";
print "Mordell-Weil subgroup";
print "P0 =", P0;
print "P1 =", P1;
print "P2 =", P2;
print "Regulator det(<D_i,D_j>) =", RegGamma;

assert RegGamma ne 0;
assert ub le 2;

// Therefore Gamma = <D1,D2> has rank 2 and finite index in J(Q).



// Effective Chabauty
//
// We use p = 7.  The same four extra residue disks appear at p = 5,
// but p = 7 is better for the sieve because
//   #J(F_7) = 528 = 2^4 * 3 * 11,
// so the odd part m = 33 gives a useful modulus.

ChabautyPrime := 7;
N := 20;
e := 50;
height_bound := 10000;

p := ChabautyPrime;
assert p notin BadReductionPrimes;

print "============================================================";
print "Effective Chabauty at p =", p;

data := coleman_data(Q, p, N);
Qpoints := Q_points(data, height_bound);

V := vanishing_differentials(Qpoints, data : e := 80);

print "Known rational Coleman points =", #Qpoints;
print "Number of vanishing differentials =", #V;

assert #V gt 0;

L, v := effective_chabauty(data : Qpoints := Qpoints, e := e);

print "Number of Chabauty candidates =", #L;

target_coords, target_keys :=
    ChabautyTargetResidueCoords(L, Qpoints, p);

assert #target_coords eq #target_keys;

print "MWS target residue classes =", target_coords;



// Mordell-Weil sieve
//
// We choose m = 33 = 3*11, the odd part of #J(F_7).
// The primes q = 31 and q = 37 both have 33 | #J(F_q).
// In the computation, q = 31 cuts each target from 33 survivors to 11,
// and q = 37 cuts the remaining survivors to 0.

m := 33;
assert GCD(TorsionBound, m) eq 1;

AuxiliaryPrimes := [31, 37];

print "============================================================";
print "Saturation for primes dividing m =", m;

for ell in PrimeDivisors(m) do
    ok := EllSaturationByReductions(C, P0, P1, P2, ell, 5000);
    assert ok;
end for;

survivors := MWSieve(
    C, P0, P1, P2, p,
    target_coords, m, AuxiliaryPrimes
);

final_counts := [ #survivors[i] : i in [1..#survivors] ];
assert &and[ c eq 0 : c in final_counts ];

print "============================================================";
print "Conclusion";
print "Effective Chabauty handles the residue disks containing the known rational points.";
print "The Mordell-Weil sieve rules out the remaining residue classes modulo", p;
print "Thus the rational points found above are all rational points on C.\n\n";



print "Going back to possible values of k, we get the following.";
pts := Setseq(Points(C : Bound := 10000));
sol := [];

for P in pts do
    if P[3] ne 0 then
        z0 := P[1]/P[3];
        w0 := P[2]/P[3]^4;   // genus 3 hyperelliptic coordinates

        A := 8*z0^3 - 2;
        B := 4*z0^4 + 8*z0^3 - 4*z0 - 1;

        if A ne 0 then
            k := (w0 - B)/(2*A);

            if k ne 0 then
                s := z0/k;
                print P, "gives k =", k, ", s =", s;

                if Denominator(k) eq 1 and k ge 1 and s^2 ne 1 then
                    Append(~sol, <Integers()!k, s>);
                end if;
            else
                print P, "gives k = 0";
            end if;
        end if;
    end if;
end for;

print "Positive integer k solutions:", sol;
assert #sol eq 0;

print "Moreover, most of the other values also degenerate the starting triple into a pair:";

function KValue(P)
    if P[3] eq 0 then return false, 0; end if;
    z0 := P[1]/P[3];
    w0 := P[2]/P[3]^4;
    A := 8*z0^3 - 2;
    B := 4*z0^4 + 8*z0^3 - 4*z0 - 1;
    if A eq 0 then return false, 0; end if;
    return true, (w0 - B)/(2*A);
end function;

for P in pts do
    ok, k := KValue(P);
    if ok then
        T := [ Rationals()!1, 2*k^2, 2*k^2 + 2*k + 1 ];
        deg := (0 in Seqset(T)) or (#Seqset(T) lt 3);
        print "P =", P, "k =", k, "triple =", T, "degenerate?", deg;
    end if;
end for;


print "Looking at the two values of k that don't degenerate our starting triple,
	 we get 2x6 torsion over Q(i), not over Q:";

Q := Rationals();
K<i> := QuadraticField(-1);


for k in [-2/3, -3/4] do
    print "k =", k;
    c := 2*k^2 + 2*k + 1;
    A := k^2*c*(2*k^2 - 1);
    B := 4*k^5*(k+1);

    E := EllipticCurve([0, A+B, 0, A*B, 0]);
    T_over_Q := TorsionSubgroup(E);
    print "torsion over Q = ", T_over_Q;
    EK := BaseChange(E, K);

    T, mp := TorsionSubgroup(EK);
    print "torsion over Q(i) =", T;

    assert Invariants(T) eq [2,6];

    print "";
end for;


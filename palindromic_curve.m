// Chabauty-Coleman + Mordell-Weil sieve for
// C: y^2 = x^8 - 4*x^7 + 4*x^6 - 28*x^5 + 70*x^4 - 28*x^3 + 4*x^2 - 4*x + 1
//
// Driver script: performs the same computation as
// quiet_simplified_CC_MWS_with_saturation_p19.m, but loads the sieve and
// saturation functions from MWS_and_saturation.m instead of defining them
// inline.
//
// Saturation note:
//   For genus 3, Magma's built-in Saturation([D1,D2], ell) is not available.
//   MWS_and_saturation.m contains a reduction-based sufficient test for
//   ell-saturation, run here at every prime dividing the main modulus.

// Parameters
ChabautyPrime := 19;
N := 20;
e := 50;
height_bound := 10000;
MainModulus := 273;        // 273 = 3*7*13 divides #J(F_19)
AuxiliaryPrimes := [11, 13, 23, 37, 43, 113];
PrintSurvivorSetsAtEnd := false;
CheckEllSaturation := true;
SaturationPrimes := PrimeDivisors(MainModulus);
SaturationSearchBound := 5000;

// Curve
Qx<x> := PolynomialRing(Rationals());
f := x^8 - 4*x^7 + 4*x^6 - 28*x^5 + 70*x^4 - 28*x^3
     + 4*x^2 - 4*x + 1;
// disc(f) = 2^40 * 3^12, so C has good reduction away from 2 and 3.

C := HyperellipticCurve(f);
J := Jacobian(C);
BadReductionPrimes := Seqset(BadPrimes(C));

// The functions in MWS_and_saturation.m use the globals BadReductionPrimes
// and PrintSurvivorSetsAtEnd; Magma resolves these when the functions are
// defined, so both must be assigned before this load.  We also load it
// before SetPath below, so that it is found in the working directory.
load "MWS_and_saturation.m";

SetPath("Classical_Chabauty");
load "coleman.m";

// Coleman needs Q in QQ[x][y]
Qxy<y> := PolynomialRing(Qx);
Q := y^2 - f;

// Chosen rational points and generators.
P0 := C![1,-1,0];
P1 := C![-1,-12,1];
P2 := C![0,-1,1];

D1 := P1 - P0;
D2 := P2 - P0;

RegGamma := Regulator([D1,D2]);

print "============================================================";
print "Height regulator =", RegGamma;
ub := RankBound(J);
print "Rank upper bound =", ub;
// Chabauty needs rank J(Q) < genus = 3: the nonzero regulator gives rank >= 2,
// and RankBound gives rank <= 2.
assert RegGamma ne 0;
assert ub le 2;
// J(Q)_tors injects into J(F_q) for every odd prime q of good reduction,
// so its order divides the bound below (= 16).  In particular J(Q) has no
// 3-, 7- or 13-torsion, which the sieve modulo 273 = 3*7*13 and the
// saturation tests both require.
torsion_bound := TorsionBound(J, 3);
print "#J(Q)_tors divides", torsion_bound;
assert GCD(torsion_bound, MainModulus) eq 1;

// Main run
print "============================================================";
print "Running effective Chabauty at p =", ChabautyPrime;
print "Main modulus =", MainModulus;
print "Auxiliary primes (q) used =", AuxiliaryPrimes;

data := coleman_data(Q, ChabautyPrime, N);
Qpoints := Q_points(data, height_bound);

print "#vanishing_differentials =", #vanishing_differentials(Qpoints, data : e := 80);

L, v := effective_chabauty(data : Qpoints := Qpoints, e := e);

print "Known rational points =", #Qpoints, "; Chabauty candidates =", #L;

target_coords, target_keys := ChabautyTargetResidueCoords(L, Qpoints, ChabautyPrime);

// A target class at infinity would be dropped from target_coords above,
// and the final SUCCESS would then be unjustified.
assert #target_coords eq #target_keys;

print "MWS target classes:", target_coords;

Cp := ChangeRing(C, GF(ChabautyPrime));
Jp := Jacobian(Cp);
print "#C(F_p) =", #Points(Cp), "; #J(F_p) =", #Jp,
      "; factorization =", Factorization(#Jp);

if CheckEllSaturation then
    print "Saturation for ell in", SaturationPrimes;
    for ell in SaturationPrimes do
        ok := EllSaturationByReductions(
            C, P0, P1, P2, ell, SaturationSearchBound
        );
        assert ok;
    end for;
end if;

survivors := MWSieve(C, P0, P1, P2, ChabautyPrime,
    target_coords, MainModulus, AuxiliaryPrimes);

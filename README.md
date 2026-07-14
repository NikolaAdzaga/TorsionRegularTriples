# TorsionRegularTriples

Magma code and logs for the paper
"Arithmetic of elliptic curves induced by regular Diophantine triples".

Each ".log" file is the complete Magma output of the corresponding ".m" file.

The Coleman integration code of Balakrishnan and Tuitman is included as the
git submodule "Classical_Chabauty", so clone with

    git clone --recursive https://github.com/NikolaAdzaga/TorsionRegularTriples

## Files by section of the paper

### Section 4 (Torsion growth over quadratic fields)
- "over_quadratic_fields.m", ".log" -- torsion growth of curves induced by
  regular triples over quadratic fields

### Section 5 (Rational points on the hyperelliptic genus 3 curve)
- "palindromic_curve.m", ".log" -- Chabauty-Coleman at p = 19 and the
  Mordell--Weil sieve for the curve C
- "MWS_and_saturation.m" sieve and saturation functions, shared by
  Sections 5 and 6

### Section 6 (About a family of induced elliptic curves)
- "CC_MWS_final_curve.m", ".log" -- rational points on the genus 3 curve C_3,
  and torsion over Q(i) for k = -2/3, -3/4
- "generic_rank_0.m", ".log" injectivity of specialization at k = 14 and
  rank E_14(Q) = 0

# OEIS A215010: equiangular polygons with sides in arithmetic progression are not only hexagons

**Source.** [A215010](https://oeis.org/A215010) (Garcia, 2012): integer side lengths t + m d of the simple convex
equiangular hexagons with sides in arithmetic progression. Comment: "Conjecture: hexagons are the only simple
convex polygons with equal interior angles with such property, due to the fact that cos(Pi/3) = 1/2." (OEIS text
checked 2026-11-06.)

**Reading.** "Such property": the n side lengths, in some order, are t, t+d, ..., t+(n-1)d with d >= 1.

**Result.** False. The equiangular 10-gon with consecutive sides t + m_k d, m = (0, 6, 2, 8, 4, 5, 1, 7, 3, 9),
closes for every t, d >= 1; for t = d = 1 its sides are 1, 7, 3, 9, 5, 6, 2, 8, 4, 10. More generally an
equiangular n-gon with sides 1, ..., n exists for many composite n (Kvant problem M644: n = 1980).

**Argument.** With w = exp(2 pi i/10), the polygon closes iff sum_k (t + m_k d) w^k = 0. The sum of all w^k is 0,
so it suffices that sum_k m_k w^k = 0. Since w^5 = -1, this is sum_(k<5) (m_k - m_(k+5)) w^k
= -5(1 - w + w^2 - w^3 + w^4) = -5 (1 + w^5)/(1 + w) = 0. (The choice m_k = 5[k odd] + (k mod 5) is a sum of a
function of k mod 2 and a function of k mod 5, and each part sums to 0 over cosets.) A closed polygon with
positive sides whose direction turns left by 2 pi/10 at every vertex (one full turn) is convex and simple, with
all interior angles 4 pi/5.

**Evidence.**
- Lean (Mathlib): [`A215010_mathlib.lean`](A215010_mathlib.lean): `A215010_offsets_perm` (m is a permutation of
  0..9, `decide`), `A215010_closes` (any primitive 10th root w, any t, d: the sum is 0), `A215010_closes_exp`
  (w = exp(2 pi i/10)). Check `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext, Classical.choice,
  Quot.sound.
- [`certificate/check.py`](certificate/check.py): floating-point closure check.
- Outside Lean: the standard fact that a closed equiangular polygon with positive sides is simple and convex.

**Review level.** `lean-proof` (closure), convexity by hand.

**Prior art.** Checked 2026-11-06. Kvant problem M644 (convex equiangular 1980-gon with sides 1..1980);
M. Bras-Amorós and M. Pujol, "Side lengths of equiangular polygons", Amer. Math. Monthly 122 (2015) 476-478
(characterises integer side-length tuples of equiangular polygons); Wikipedia "Equiangular polygon" (prime n
forces regular). The entry comment is not annotated. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.

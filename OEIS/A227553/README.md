# OEIS A227553: number of solutions of x^2 - y^2 - z^2 ≡ 1 (mod p^s)

**Source.** OEIS [A227553](https://oeis.org/A227553): number of solutions of x^2 - y^2 - z^2 ≡ 1
(mod n). Conjecture: "a(2) = 4; if s > 1 then a(2^s) = 2^(2s-1); if p == 1 (mod 4) then a(p^s) =
(p+1)*p^(2s-1); if p == 3 (mod 4) then a(p^s) = (p-1)*p^(2s-1)." (OEIS text, CC BY-SA 4.0.)
(The scan's record misquotes the odd case as p(p±1)^(2s-1); the entry's formula is the one above
and is the one proved.)

**Result.** True.

**Argument.**
- p odd, s = 1. Substitute u = x - y, v = x + y (invertible since 2 is a unit): uv = 1 + z^2. For
  each z, if 1 + z^2 ≢ 0 there are p - 1 pairs (u, v); if 1 + z^2 ≡ 0 there are 2p - 1. The number of
  z with z^2 ≡ -1 is 2 if p ≡ 1 (mod 4) and 0 if p ≡ 3. Total p(p-1) + 2p = p(p+1), resp. p(p-1).
- p odd, lifting. Every solution mod p is nonsingular (the gradient (2x, -2y, -2z) vanishes only at
  0, which is not a solution), so by Hensel each solution mod p^s has exactly p^2 lifts mod
  p^(s+1): a(p^s) = (p ± 1) p · p^(2(s-1)) = (p ± 1) p^(2s-1).
- p = 2. a(2) = 4 directly. For s ≥ 2: x must be odd (if x is even, y^2 + z^2 ≡ x^2 - 1 ≡ 3
  (mod 4), impossible). For given y, z the number of x mod 2^s with x^2 ≡ A := 1 + y^2 + z^2 is 2
  (s = 2) or 4 (s ≥ 3) when A ≡ 1 (mod 4) resp. (mod 8), and 0 otherwise. A ≡ 1 (mod 8) iff
  y^2 + z^2 ≡ 0 (mod 8) iff y ≡ z ≡ 0 or y ≡ z ≡ 2 (mod 4): 2^(2s)/8 pairs; A ≡ 1 (mod 4) iff y,
  z both even: 2^(2s)/4 pairs. So a(4) = 2·4 = 8 and a(2^s) = 4·2^(2s-3) = 2^(2s-1) for s ≥ 3.

**Evidence.**
- `certificate/a227553.py`: direct counts for all prime powers p^s ≤ 1100 (p < 60) agree.
- [`A227553_mathlib.lean`](A227553_mathlib.lean) (Mathlib): `A227553_main` proves all four
  statements for a(n) = `Nat.card` of the solutions in `ZMod n`. Odd p uses the uv = 1 + z^2
  form split by which of u, v are units (no Hensel induction: square roots of elements ≡ -1 mod p
  come from injectivity of squaring on elements ≡ 1 mod p); p = 2 uses the fibre over (y, z) with
  exactly 4 square roots of each A ≡ 1 (mod 8) for s ≥ 3, and `decide` for a(2), a(4). Outside
  Lean: nothing.

**Review level.** `lean-proof` ([`A227553_mathlib.lean`](A227553_mathlib.lean), all cases).
Before: `rechecked` (argument re-derived; the scan cited a Gauss-sum formula and "direct count"
for p = 2; the count above covers all s).

**Depends on (Mathlib).** -1 is a square mod p iff p ≡ 1 (mod 4) (in Mathlib), Hensel's lemma (in
Mathlib), counting squares mod 2^s.

**Prior art.** Partly known. [OEIS A227553](https://oeis.org/A227553) (fetched 2026-11-04) still says Conjecture. Its linked [Tóth (2014)](https://cs.uwaterloo.ca/journals/JIS/VOL17/Toth/toth12.html), Prop. 14 (E. Cohen's formula, odd moduli) gives the odd prime-power cases directly; the 2-power cases are not covered there. Searched: entry, OEIS cross-reference search, edit history, Tóth full text. Worth an OEIS comment. (Prior-art review 2026-11-04.)

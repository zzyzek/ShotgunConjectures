# OEIS A216371: for odd primes with one coach, the top row is a permutation of 1, 3, ..., 2q-1

**Source.** OEIS [A216371](https://oeis.org/A216371) (Gary W. Adamson, Sep 05 2012): odd primes p with
A135303((p-1)/2) = 1, where A135303(n) = phi(2n+1)/(2 A003558(n)) is the number of coaches of 2n+1 and A003558(n)
is the least m > 0 with 2^m = +-1 (mod 2n+1). Conjecture (Adamson, Sep 08 2012): if p is a term and p = 4q-1 or
4q+1, the top row of its coach is a permutation of the first q odd integers (11: [1, 5, 3]; 13: [1, 3, 5];
37: [1, 9, 7, 15, 11, 13, 3, 17, 5]). (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** Hilton-Pedersen coach of an odd b: starting from a_1 = 1, write b - a_i = 2^(k_i) a_(i+1) with
a_(i+1) odd, until a_(i+1) = 1; the top row is a_1, ..., a_r (the bottom row holds the k_i). This reproduces the
three examples. In both cases q = floor((p+1)/4).

**Result.** True for every term p.

**Argument.** Let p = 2r+1 and S = {1, ..., r}. The folded doubling h(x) = 2x (if 4x < p) or p - 2x maps S to S
and is multiplication by 2 on the classes {+-x} mod p, so h^j(1) = +-2^j. If no 0 < m < r has 2^m = +-1 (mod p)
(Greathouse's characterization of the terms), the values h^j(1), j < r, are distinct, so h is one r-cycle on S.
A coach step a -> c = odd part of p - a is undone by doubling: h^i(c) = 2^i c is even for 0 < i <= k-1 and
h^k(c) = p - 2^k c = a. Hence c is the previous odd value before a along the h-cycle, so the coach map is a
bijection of the odd elements of S and its orbit from 1 runs backward through all of them: the top row is a
permutation of the q odd numbers 1, 3, ..., 2q-1 in S. Terms satisfy Greathouse's condition: by Fermat
(2^r)^2 = 1, so 2^r = +-1 and A003558(r) divides r; A135303 = 2r/(2 A003558(r)) = 1 then forces A003558(r) = r.

**Evidence.**
- Lean (Mathlib): [`A216371_mathlib.lean`](A216371_mathlib.lean). Main theorem `A216371_coach`: for p prime,
  2 < p, `coaches ((p-1)/2) = 1` (A135303 with `sord` = A003558 as `Nat.find`), `(f p)^[(p+1)/4] 1 = 1`, no earlier
  return to 1, and `[(f p)^[j] 1 | j < (p+1)/4]` is a permutation of `[2i+1 | i < (p+1)/4]`. Route in the file
  header. `tools/leancheck-mathlib.sh`: OK, no warnings; axioms propext, Classical.choice, Quot.sound.
- [`certificate/coach.py`](certificate/coach.py): for all primes 3 <= p < 20000 the top row is a permutation of
  the first q odd numbers exactly when A135303((p-1)/2) = 1 (1258 terms).
- Outside Lean: none beyond the reading of "coach".

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The statement follows from the coach theory of P. Hilton and J. Pedersen
(*A Mathematical Tapestry*, CUP 2010, pp. 260-264, cited in the entry): the coaches of b partition the odd numbers
below b/2 coprime to b, and phi(b) = 2ck. With c = 1 and b prime the single coach holds all of them. The entry
leaves Adamson's comment unannotated. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

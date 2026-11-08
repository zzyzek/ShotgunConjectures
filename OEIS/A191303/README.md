# OEIS A191303: polynomials with only k-digit half-palindrome values exist for k = 5, …, 11 and 13

**Source.** OEIS [A191303](https://oeis.org/A191303) (an infinite sequence of 4-digit
half-palindromes), comment by Vladimir Shevelev: "Conjecture. For every k>=2, there exists a
polynomial of degree k taking only k-digit half-palindrome values." The entry adds that for
k ≥ 5 it is unknown whether such polynomials exist. Definition (A191279): m is a k-digit
half-palindrome if m = [m_1 … m_k]_b = [m_k … m_1]_c for some bases 1 < b < c, all m_i digits
in both bases, m_1 > 0, m_k > 0. (OEIS text, CC BY-SA 4.0.)

**Result (partial; the conjecture stays open for k = 12 and k ≥ 14).** For each k = 5, …, 11 and k = 13 there is an
explicit polynomial P_k of degree k with P_k(s) a k-digit half-palindrome for every s ≥ 0. Base
b, second base c and all digits are linear in s:

| k | b | c | digits m_1, …, m_k |
|---|---|---|---|
| 5 | 8s+14 | 8s+16 | s+1, 8s+13, 2s+3, 2, s+1 |
| 6 | 2s+5 | 2s+6 | s+3, s, 2s+3, 3, 1, s+1 |
| 7 | 2s+7 | 2s+8 | s+5, s+3, 2s+2, s+3, 5, s+3, s+2 |
| 8 | 22s+24 | 22s+25 | s+1, 8s+9, 8s+9, 11s+12, 12s+13, 3s+3, s+1, s+1 |
| 9 | 20s+63 | 20s+64 | s+2, 18s+55, 6s+18, 18s+61, 15s+50, 4s+8, 8s+24, 10s+34, s+2 |
| 10 | 22s+223 | 22s+224 | (see `certificate/shifted.txt`) |
| 11 | 14s+170 | 14s+171 | (see `certificate/shifted.txt`) |
| 13 | 60s+98 | 60s+99 | s+1, 24s+37, 25s+38, 10s+20, 30s+60, 18s+27, 27s+29, 6s+12, 11, 20s+29, 7s+8, 12s+22, s+1 |

For example k = 5, s = 0: 74705 = [1, 13, 3, 2, 1]_14 = [1, 2, 3, 13, 1]_16.

**Method.** With b = αt + β, c = b + d and digits a_i t + e_i, the identity
Σ m_i b^{k−i} = Σ m_i c^{i−1} is k + 1 linear equations in the 2k integers (a_i, e_i). The
integer solutions form a lattice; its projection to the slopes a is enumerated in Hermite
normal form over the box 0 ≤ a_i ≤ α, keeping solutions whose digits are valid for all large t
(a_i = 0 needs e_i ≥ 0, a_i = α needs e_i < β). `certificate/enum3.gp` (with `lat.gp`)
searches α ≤ 24 (k ≤ 8), α ≤ 40 (k = 9), α ≤ 80 with d = 1 (k = 10, 11), α ≤ 160 with d = 1
and α ≤ 40 with d ≤ 4 (k = 12), α ≤ 60 with d = 1 (k = 13) and α ≤ 120 with d = 1 (k = 14); `certificate/shift.py` shifts t so all digits are valid from s = 0 and re-verifies
the identities with sympy.

Two structural facts found on the way. Writing digits as u_i X + v_i in X = b, the identity
reads V(X) − V*(X + d) = X (U*(X + d) − U(X)) (stars: reversed coefficient lists), and the
map V ↦ V(X) − V*(X + d) is the Sym^{k−1} action of [[0, 1], [1, d]] minus the identity, whose
eigenvalues λ^j μ^{k−1−j} (λμ = −1, λ > 1) equal 1 only for k ≡ 1 (mod 4), j = (k − 1)/2. So for
k ≢ 1 (mod 4) every slope vector u with u_1 = u_k extends to a rational solution; the obstruction
to large k is integrality (the slopes must lie in a lattice whose covolume grows with k), not
the real identity. For k = 12 and k = 14 no family exists in the searched ranges; k = 13 (≡ 1 mod 4, where the
solution space is one dimension larger) has one.

**Evidence.**
- Lean (Mathlib): [`A191303_mathlib.lean`](A191303_mathlib.lean). `A191303_k5`, …,
  `A191303_k11`, `A191303_k13`: for every s : ℕ, `HalfPal k (P_k s)` (definition of A191279 with explicit
  digit lists and `valB`), by `ring` and `omega`. Axioms propext, Classical.choice, Quot.sound;
  zero warnings. Outside Lean: that P_k has degree k is read off its explicit coefficients; the
  search scripts (not needed for the result).
- `certificate/hits.txt`, `certificate/shifted.txt` (raw and shifted families).

**Review level.** `lean-proof` (for k = 5, …, 11 and 13).

**Prior art.** The entry (cached, 2026-11-07) states that k ≥ 5 is open. google-deepmind/
formal-conjectures (clone of 2026-11-06) and otoi-lab/oeis-lean-proofs have no file for A191303
or A191279.

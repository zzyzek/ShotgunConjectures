# OEIS A229136: a(n) = A131885(n) * 2^(n-1) (proved in the entry, reproved in Lean)

**Source.** [A229136](https://oeis.org/A229136) (offset 1), "Number of solutions to Sum_{i=1..n} x_i^2
== 1 (mod 4) with x_i in 0..3." Comment: "Conjecture: a(n) = A131885(n)*2^(n-1) for n >= 1.
[Corrected by Petros Hadjicostas, Dec 20 2019]". [A131885](https://oeis.org/A131885): a(0..3) = 1, 2,
4, 6 and a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) for n >= 4. (OEIS text, CC BY-SA 4.0; A229136 revision
#55 of Aug 16 2025, checked 2026-11-06.)

**Reading.** The scan record quotes the older form a(n) = A131885(n)*2^n, which is false for every
n >= 1 (a(1) = 2, A131885(1)*2 = 4); the exponent n-1 is the entry's current text and matches the
data.

**Result.** True for every n >= 1: a(n) = A131885(n) * 2^(n-1). Already proved in the entry by
P. Hadjicostas (Dec 20 2019) from the recurrence a(n) = 4a(n-1) - 8a(n-2) + 2^(2n-3), which he takes
from the theory of A330619. The argument below is self-contained.

**Argument.** Let c_r(n) count the vectors in {0..3}^n with sum of squares = r mod 4. The squares
of 0, 1, 2, 3 are 0, 1, 0, 1 mod 4, so splitting off x_1 gives c_r(n+1) = 2 c_r(n) + 2 c_{r-1}(n)
(indices mod 4), with c(0) = (1, 0, 0, 0). Then c_0 - c_1 + c_2 - c_3 = 0 for n >= 1 (each step maps
the alternating sum to 0). In vector form c(n+1) = 2(I + P)c(n) with P the cyclic shift, and
8(I+P)^3 - 32(I+P)^2 + 48(I+P) - 32 I = -8(I - P + P^2 - P^3), whose residue-1 row is 8 times the
alternating sum. So c_1(n+4) = 8c_1(n+3) - 24c_1(n+2) + 32c_1(n+1) for n >= 0. With c_1(1), c_1(2),
c_1(3) = 2, 8, 24 = A131885(n)*2^(n-1) for n = 1, 2, 3, induction gives the formula, since
2^(n+3) A131885(n+4) = 8*2^(n+2)A131885(n+3) - 24*2^(n+1)A131885(n+2) + 32*2^n A131885(n+1).

**Evidence.**
- Lean (Mathlib): [`A229136_mathlib.lean`](A229136_mathlib.lean). `cnt n r` counts
  `x : Fin n → Fin 4` with `(∑ x_i^2) % 4 = r`, `A229136 n = cnt n 1`, `A131885` by its defining
  recurrence. Main theorem `A229136_formula : 1 ≤ n → (A229136 n : ℤ) = A131885 n * 2^(n-1)`;
  `scan_form_false` (the 2^n form fails at n = 1). Steps `cnt_succ`, `alt`, `rec1`. Checked with
  `tools/leancheck-mathlib.sh`: OK, no warnings; axioms propext, Classical.choice, Quot.sound.
  No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): brute force for n <= 8, residue DP and the formula
  for n <= 200, the 26 data terms.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Proof in the entry by P. Hadjicostas (Dec 20 2019, revisions
#46-#55), resting on the recurrence for column k = 1 of A330619. Not in
google-deepmind/formal-conjectures (tree at HEAD 2026-11-06) or otoi-lab/oeis-lean-proofs; no Lean
proof found before this.

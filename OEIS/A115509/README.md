# OEIS A115509: a(n) = 0 for 2^(k+1) ≤ n < 3·2^k

**Source.** OEIS [A115509](https://oeis.org/A115509) (Max Alekseyev, 2006): "Number of circular
permutations of {1, 2, ..., n} such that in every pair of adjacent elements each element in binary
notation has ones at the same or adjacent positions to those of the other element." The statement
"If 2^(k+1) <= n < 3*2^k for k >= 1, then a(n) = 0" was a conjecture on the OEIS wiki list
(Talk:Conjectures/List) and became a plain FORMULA line in rev. #6 (2023-03-18) with no proof
recorded. (OEIS text, CC BY-SA 4.0.)

**Reading.** x and y may be adjacent when every 1-bit of x has a 1-bit of y at the same or a
neighbouring position, and vice versa. Circular permutations are counted up to rotation only (the
data has a(3) = 2, so the two orientations count separately); we count arrangements that start with 1.

**Result.** True for every k ≥ 1; proved in Lean 4 + Mathlib.

**Argument.** Let m = 2^(k+1) ≤ n < 3·2^k, so n ≥ 4. A neighbour y of m has all its 1-bits at
positions k, k+1 or k+2, so 2^k divides y; 1 ≤ y < 3·2^k leaves y = 2^k or y = 2^(k+1) = m.
On a circle of n ≥ 4 distinct numbers, m has two distinct neighbours, both different from m,
so both would equal 2^k. Hence no arrangement exists and a(n) = 0.

**Evidence.**
- Lean (Mathlib): [`A115509_mathlib.lean`](A115509_mathlib.lean). Definitions `near`, `good`,
  `cyclicGood` (consecutive pairs and the last/first pair), `arrangements n` (permutations of
  [1..n] starting with 1 that satisfy `cyclicGood`), `A115509 n := (arrangements n).card`.
  - `neighbour_eq`: 1 ≤ y < 3·2^k and `near y (2^(k+1))` imply y = 2^k ∨ y = 2^(k+1).
  - `A115509_no_cycle`: for 1 ≤ k, 2^(k+1) ≤ n < 3·2^k, no permutation of [1..n] (any start)
    satisfies `cyclicGood`.
  - `A115509_formula`: under the same hypotheses, `A115509 n = 0`.
  Check: `tools/leancheck-mathlib.sh OEIS/A115509/A115509_mathlib.lean` → OK, no warnings.
  Axioms: `propext, Classical.choice, Quot.sound` (printed as `choice` because the file opens
  `Classical`). No `sorry`, no `native_decide`.
- [`certificate/check_A115509.py`](certificate/check_A115509.py): Hamiltonian-cycle DP from the
  same definition reproduces a(1..16) of the entry.
- Outside Lean: none for the formula. The listed terms are checked only by the script.

**Review level.** `lean-proof` (re-derived; the whole statement is proved in Lean).

**Prior art.** Known: the formula is in the entry since 2023 (rev. #6, M. Alekseyev) without a
written proof; the argument above is immediate. google-deepmind/formal-conjectures has no
`FormalConjectures/OEIS/115509.lean`, and otoi-lab/oeis-lean-proofs has no file for it (checked
2026-11-05). (Prior-art review 2026-11-05.)

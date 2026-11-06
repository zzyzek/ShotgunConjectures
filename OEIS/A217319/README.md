# OEIS A217319: the P-positions of Mark-4 are 0 and the numbers with odd 4-adic valuation

**Source.** OEIS [A217319](https://oeis.org/A217319), numbers whose binary representation ends in
4k+2 or 4k+3 zeros. Formula line: "Conjecture. For n>=1, a(n) = A171949(n+1)." OEIS
[A171949](https://oeis.org/A171949), P-positions of the game Mark-4, carries the same conjecture
(V. Shevelev, Mar 2013). (OEIS text, CC BY-SA 4.0; both still conjectures on 2026-11-06.)

**Reading.** Mark-t (A. S. Fraenkel): from n a player moves to n−1, ..., n−(t−1) (staying ≥ 0) or to
⌊n/t⌋; the player unable to move loses (definition as in Guo, arXiv:1108.1239, Sec. 1). For t = 4, 0 is
the first P-position (A171949(1) = 0) and A217319 is the set of n ≥ 1 with odd 4-adic valuation (binary
trailing-zero count ≡ 2, 3 mod 4), so the conjecture says: P-positions = {0} ∪ {n ≥ 1 : v_4(n) odd}.

**Result.** True; known (Fraenkel 2012, for every t: the P-positions of Mark-t are the numbers with an odd
number of trailing zeros in base t). Reproved here in core Lean.

**Argument.** Let D = {0} ∪ {n : v_4(n) odd}. No move joins two members of D: for n ∈ D, n > 0, 4 | n and
n/4 ∉ D; the moves n−1, n−2, n−3 are positive and not divisible by 4, so not in D, and ⌊n/4⌋ = n/4 ∉ D.
Every n ∉ D (so n > 0) has a move into D: if 4 | n then n/4 ∈ D; if r = n mod 4 ≠ 0, either n − r ∈ D, or
n − r = 4q with q ≥ 1 and q ∈ D, and then ⌊n/4⌋ = q. Since moves decrease n, these two facts give
P-positions = D by strong induction.

**Evidence.**
- Lean (core): [`A217319.lean`](A217319.lean). `A217319_isP` defines P-positions of Mark-4 by well-founded
  recursion from the move relation `A217319_move`. `A217319_main`: A217319_isP n ↔ (n = 0 ∨ ∃ k m,
  m % 4 ≠ 0 ∧ n = 4^(2k+1)·m). Lemmas `A217319_noPP`, `A217319_toP`, `A217319_isP_iff_D`, `A217319_D_iff`.
  Axioms: propext, Quot.sound, Classical.choice (the last only via `A217319_D_pow`/`A217319_D_iff`).
- `certificate/check.py`: brute-force Mark-4 outcomes for n < 200000 agree with D and with the OEIS data.
- Outside Lean: that `A217319_move` transcribes Fraenkel's Mark-4, and that A217319's binary description
  equals odd 4-adic valuation (immediate: v_2 ≡ 2, 3 mod 4 ⇔ ⌊v_2/2⌋ odd).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: A. S. Fraenkel, "The vile, dopey, evil and odious game players",
Discrete Math. 312 (2012) 42–46 (linked from A171949) introduces Mark-t; A. Guo, "Winning strategies for
aperiodic subtraction games", arXiv:1108.1239 (2011), Sec. 2, states that the P-positions of Mark-t are the
numbers with an odd number of trailing zeros in base t, citing Fraenkel, and builds his Sprague–Grundy
analysis on it. For t = 4 this is the conjecture. Fraenkel's paper itself was not read here (paywalled);
the attribution rests on Guo. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs
(local clones, 2026-11-05 and 2026-10-13). The companion record OEIS-A171949 is the same statement.

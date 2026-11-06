# OEIS A097602: the squares hit are exactly m² with 3 ∤ m

**Source.** [A097602](https://oeis.org/A097602) (offset 1), Reinhard Zumkeller, Aug 30 2004: "a(n+1) = a(n) +
number of squares so far; a(1) = 1." Comment: "Conjecture: a(n) = m^2 iff m mod 3 > 0." The entry also carries,
credited to Vladeta Jovovic (2004, added in revision #16, May 10 2013), "a(n) is a square iff n is congruent to
{1, 4} mod 9", the formulas a(9n+1) = (3n+1)², a(9n+4) = (3n+2)² and a rational g.f., all without proof.
(OEIS text, CC BY-SA 4.0, revision #22 of Sep 22 2025, checked 2026-11-06.)

**Reading.** "Squares so far" counts the squares among a(1), ..., a(n), including a(n) (the entry's example
a(2) = 1 + 1 confirms this). The conjecture reads: m² is a term of the sequence iff m mod 3 ≠ 0 (m = 0 included:
0 is not a term).

**Result.** True. For every k ≥ 0, with c the running count of squares,
a(9k+1) = (3k+1)² (c = 2k+1), a(9k+2), a(9k+3) = (3k+1)² + (2k+1), + 2(2k+1),
a(9k+4) = (3k+2)² (c = 2k+2), a(9k+5), a(9k+6) = (3k+2)² + (2k+2), + 2(2k+2),
a(9k+7) = (3k+3)² + 1, a(9k+8), a(9k+9) = (3k+3)² + 1 + (2k+2), + 2(2k+2).
So a(n) is a square iff n ≡ 1, 4 (mod 9) (Jovovic's claims), and the squares hit are (3k+1)², (3k+2)².

**Argument.** Induction on k. At a(9k+1) = (3k+1)² the count is 2k+1 (the squares (3j+1)², (3j+2)² for j < k and
(3k+1)²). Since (3k+2)² − (3k+1)² = 6k+3 = 3(2k+1), three steps reach (3k+2)², and the two intermediate values lie
strictly between consecutive squares. Now c = 2k+2 and (3k+3)² − (3k+2)² = 6k+5 = 3(2k+2) − 1, so the third
step lands on (3k+3)² + 1, skipping (3k+3)²; again nothing in between is square. Then (3k+4)² − ((3k+3)² + 1) =
6k+6 = 3(2k+2), so three more steps reach (3k+4)², with count 2k+3 = 2(k+1)+1. The base case is a(1) = 1, c = 1.

**Evidence.**
- Lean (Mathlib): [`A097602_mathlib.lean`](A097602_mathlib.lean). Definitions: `st i = (a(i+1), count)` by
  recursion, `A097602 n = (st (n−1)).1`. Theorems: `A097602_succ` (a(n+1) = a(n) + #{1 ≤ i ≤ n : IsSquare a(i)},
  that is the OEIS definition), `A097602_one`, `closed_form` (the nine values of block k), `A097602_9k1`,
  `A097602_9k4`, `A097602_isSquare_iff` (n ≥ 1: a(n) square ⇔ n mod 9 ∈ {1, 4}), `A097602_conjecture`
  ((∃ n ≥ 1, a(n) = m²) ⇔ m % 3 ≠ 0, for all m).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: propext, Classical.choice, Quot.sound
  (`not_sq` only propext, Quot.sound). No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): 300000 terms from the definition match the closed form, and the
  conjecture holds for m < 100000; the OEIS b-file (n ≤ 10000) matches.
- Outside Lean: none. Not verified in Lean: agreement with the b-file (check.py) and Jovovic's g.f. (not treated).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry and its history (to revision #22) state Jovovic's formulas and the
"n ≡ 1, 4 (mod 9)" characterisation since revision #16 (2013) without proof; together they imply the conjecture.
No proof found by web search. Not in google-deepmind/formal-conjectures (no `A097602` file in the tree at HEAD)
or otoi-lab/oeis-lean-proofs.

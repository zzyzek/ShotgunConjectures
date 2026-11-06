# OEIS A007669: A007669(n) = A178717(n−1) − 1 is false (first failure n = 8)

**Source.** [A007669](https://oeis.org/A007669) (offset 1), now dead: "Duplicate of A034343". Former name "Number of
orthogonal lattices in dimension n" (Schwarzenberger), data 1, 2, 4, 8, 16, 36, 80 until 2017. Comment, in the entry
from Sep 2010 until revision #12 (Nov 27 2017): "Conjecture (V. Kotesovec, 2010): a(n) = A178717(n-1) - 1".
(OEIS text, CC BY-SA 4.0.) [A178717](https://oeis.org/A178717) (offset 1): degree of the denominator of the GF for
k nonattacking queens on an n × n board, with Kotesovec's explicit formula
d(k) = 2k + 1 + Σ_{j=1}^{k−1} Σ_{i=F(k−j)+1}^{F(k−j+1)} 2j φ(i) (k > 1).

**Reading.** A007669 is read as [A034343](https://oeis.org/A034343) (Sloane's identification, via Schwarzenberger's
theorem): the number of binary linear codes of length n, any dimension, with no zero column, up to permutation of
coordinates (= loopless binary matroids on n points). A178717 is read through Kotesovec's formula, from which its data
are computed.

**Result.** False. The conjecture was made on the seven terms known in 2010 (it holds for 2 ≤ n ≤ 7). With
A034343(8) = 194 (data since the 2017 merge; Fripertinger, Wild) and A178717(7) = 197, it fails at n = 8:
194 ≠ 196. It fails again at n = 9 (506 ≠ 476) and for every n ≥ 9 in the data; a(n) grows like 2^{n²/4}/n!,
A178717 only like φ^{2n}.

**Argument (Lean, n = 20).** The 10 × 10 matrices A over GF(2) with no zero row give (2¹⁰ − 1)¹⁰ = 1023¹⁰ different
codes {(x, Ax)} of length 20 with no zero column. Each equivalence class is the image of the symmetric group, so it has
at most 20! members, and a(20) ≥ 1023¹⁰/20! > 5.15 · 10¹¹. Kotesovec's formula with φ(i) ≤ i ≤ F(19) = 4181 gives
A178717(19) ≤ 39 + 18 · 4181 · 38 · 4181 < 1.2 · 10¹⁰ (actual value 17202449). So a(20) ≠ A178717(19) − 1.

**Evidence.**
- Lean (Mathlib): [`A007669_mathlib.lean`](A007669_mathlib.lean), namespace `A007669`. `a n` = Nat.card of the
  quotient of `Code n` (submodules of `Fin n → ZMod 2` with no zero coordinate) by coordinate permutation. Theorems
  `card_code_le` (|Code n| ≤ n! · a n), `card_code_20` (1023¹⁰ ≤ |Code 20|), `a_20_ge` (515978636151 ≤ a 20),
  `A178717_19_le`, main `A007669_conj_false : a 20 ≠ A178717 19 - 1`. Check: `tools/leancheck-mathlib.sh`, exit 0,
  no warnings; axioms propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`.
- [`certificate/burnside.py`](certificate/burnside.py): enumerates all subspaces of GF(2)^n, n ≤ 9, and counts
  permutation classes of those without zero column by Burnside's lemma: 1, 2, 4, 8, 16, 36, 80, 194, 506, equal to
  the A034343 data; evaluates Kotesovec's formula (equal to the A178717 data for k ≤ 20). Log:
  [`certificate/burnside9.log`](certificate/burnside9.log).
- Outside Lean: the two readings above (dead entry = A034343; A178717 = Kotesovec's formula), and the first failure
  at n = 8 (Python Burnside count and published data; Lean proves a failure at n = 20).

**Review level.** `lean-proof` for the failure at n = 20 under the stated readings; `rechecked` for n = 8, 9.

**Prior art.** Checked 2026-11-06. The published values refute it: A034343(8) = 194 (Fripertinger 1995–97, Wild 1994;
the 2017 merge put these values into A007669, and the conjecture comment was dropped when the entry was made dead) and
A178717(7) = 197. No one states the refutation explicitly that we found. Not in google-deepmind/formal-conjectures
(clone 2026-11-05) or otoi-lab/oeis-lean-proofs (clone 2026-10-13).

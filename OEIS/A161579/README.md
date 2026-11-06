# OEIS A161579 (with A161580, A161817, A161890, A162311): alternation of odious and evil solutions

**Source.** V. Shevelev, 2009, in [A161579](https://oeis.org/A161579) (t(n) = t(n+3)),
[A161580](https://oeis.org/A161580) (t(n) + t(n+3) = 1), [A161817](https://oeis.org/A161817) (k = 5),
[A162311](https://oeis.org/A162311) (k = 7), [A161890](https://oeis.org/A161890) (k = 9), where t = A010060
is the Thue–Morse sequence: "In every sequence of numbers n such that A010060(n)=A010060(n+k), for fixed
odd k, the odious (A000069) and evil (A001969) terms alternate" (A161580: the same for
A010060(n)+A010060(n+k)=1). (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** Odious: t(n) = 1; evil: t(n) = 0. "Alternate": consecutive solutions n < n' (no solution
strictly between) have t(n) ≠ t(n').

**Result.** True for every odd k, for both equations. Known: A161890 carries the comment (J. Shallit,
Oct 12 2022) that the conjecture was proved in a later version of Shevelev's arXiv:0907.0880 and can be
proved with Walnut. Reproved here with a short argument and a full Lean proof.

**Argument.** Let P(n) = Σ_{m<n} (-1)^t(m). Since t(2j+1) = 1 - t(2j), P(2j) = 0 and
P(2j+1) = (-1)^t(j). Let Q(n) = Σ (-1)^t(m) over m < n with t(m) = t(m+k). Because
(-1)^t(m) [t(m) = t(m+k)] = ((-1)^t(m) + (-1)^t(m+k))/2, 2Q(n) = P(n) + P(n+k) - P(k). For odd k,
one of n, n+k is even, so 2Q(n) = ±1 - σ with σ = P(k) = ±1, i.e. Q(n) ∈ {0, -σ} for all n. Each
solution changes Q by (-1)^t(m) = ±1 and non-solutions leave it fixed; a sequence staying in a set of
two adjacent integers must step alternately up and down, so consecutive solutions have opposite
(-1)^t. For t(m) + t(m+k) = 1 the same works with 2R(n) = P(n) - P(n+k) + P(k), R(n) ∈ {0, σ}.

**Evidence.**
- Lean (Mathlib): [`A161579_mathlib.lean`](A161579_mathlib.lean), with `tm n = (Nat.digits 2 n).sum % 2`.
  Main theorems `alternate_eq` and `alternate_ne`: for odd k, n < n' solutions with no solution
  strictly between, `tm n ≠ tm n'`. Axioms propext, Classical.choice, Quot.sound.
- `certificate/check.py`: alternation for odd k ≤ 51, n < 200000, both equations.
- Outside Lean: none.

**Review level.** lean-proof.

**Prior art.** Checked 2026-11-06. The A161890 comment by J. Shallit (2022) states the conjecture was
proved in a later version of arXiv:0907.0880 (v7, 2012) and is Walnut-provable for each k; the arXiv
abstract only says that conjectures are posed (the proof text was not read here). Allouche
(arXiv:1401.3727, JTNB 2015) proves a conjecture of Shevelev (which one was not checked). No Lean
proof in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

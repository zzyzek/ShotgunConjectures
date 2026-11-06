# OEIS A064016: the limit comment is misstated; a(n)/10^(2n) → 1/2 − 3/π² (Mertens)

**Source.** [A064016](https://oeis.org/A064016), "a(n) = Sum_{k <= 10^n} cototient(k), where cototient is
A051953." Comment: "It appears that lim_{n->infinity} (1/n^2) * Sum_{j=1..n} a(j) = 0.1960364... = (1/2 -
3/Pi^2)." (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** As printed the claim is about (1/n^2) Σ_{j≤n} a(j). The constant 1/2 − 3/π² is the density of
Σ_{k≤N} cototient(k) / N^2, so the intended statement is a(n)/10^(2n) → 1/2 − 3/π² (equivalently
Σ_{k≤N} (k − φ(k)) ~ (1/2 − 3/π²) N^2).

**Result.** As printed: false, (1/n^2) Σ_{j≤n} a(j) → +∞ (a(n) grows like 100^n). Intended: true,
a(n)/10^(2n) → 1/2 − 3/π² = 0.19603644907..., by Mertens' theorem Σ_{k≤N} φ(k) = 3N²/π² + O(N log N) (1874).

**Argument.** φ = μ ∗ id, so Σ_{n≤N} φ(n) = Σ_{d≤N} μ(d) T(⌊N/d⌋) with T(M) = M(M+1)/2. Each term divided by
N^2 tends to μ(d)/(2d²) and is bounded by 1/d², so by dominated convergence the ratio tends to
(1/2) Σ μ(d)/d² = (1/2)/ζ(2) = 3/π². Subtracting from Σ_{k≤N} k = N(N+1)/2 gives the cototient sum. For the
printed form, a(n) ≥ (c/2)·100^n eventually (c = 1/2 − 3/π² > 0) and 100^n ≥ n³, so the average is at least
(c/2)·n.

**Evidence.**
- Lean (Mathlib): [`A064016_mathlib.lean`](A064016_mathlib.lean). `a n = Σ_{k ∈ Icc 1 (10^n)} (k − φ k)` as in the
  entry. Theorems: `sum_totient_tendsto` (Σ_{k≤N} φ(k)/N² → 3/π²), `sum_cototient_tendsto`,
  `A064016_tendsto` (a(n)/(10^n)² → 1/2 − 3/π²), `A064016_literal_false` ((Σ_{j=1..n} a(j))/n² → ∞). Uses
  Mathlib's `LSeries_zeta_mul_Lseries_moebius`, `riemannZeta_two` and Tannery's theorem.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): recomputes a(0..6) (matches the data) and the ratios.
- Outside Lean: none (the reading of the intended statement is stated above).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The intended statement is Mertens' theorem on Σ φ(k) (F. Mertens, J. reine
angew. Math. 77 (1874); Hardy–Wright Thm 330). No Lean proof of the totient-sum asymptotic in Mathlib (revision
56a0058), google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06). The
divergence of the printed average is immediate.

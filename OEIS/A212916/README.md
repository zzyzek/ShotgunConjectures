# OEIS A212916: standard Young tableaux of height ≤ 10, a(n) ~ 10^n π^(−5) (10/n)^(45/2) ∏ Γ(j/2)

**Source.** OEIS [A212916](https://oeis.org/A212916) (offset 0): number of standard Young tableaux with n
cells and at most 10 rows. Conjecture (V. Kotesovec, Sep 12 2013): "generally (for tableaux with height
<= k), a(n) ~ k^n/Pi^(k/2) * (k/n)^(k*(k-1)/4) * prod(j=1..k,Gamma(j/2)); set k=10 for this sequence."
(OEIS text, CC BY-SA 4.0; revision #32.) The same general conjecture is in A229068 (k = 12), see
[`../A229068/README.md`](../A229068/README.md).

**Result.** True for every k ≥ 1, by a theorem of Regev (1981).

**Argument.** Let S_k(n) = Σ f^λ over partitions λ ⊢ n with at most k rows. A. Regev, Asymptotic values for
degrees associated with strips of Young diagrams, Adv. Math. 41 (1981) 115–136, Corollary 4.4, restated with
d = α = 1 as Theorem 3.5 of A. Regev, Asymptotics of Young tableaux in the strip, the d-sums,
arXiv:1004.4476 (there T_{1,s}(m) = S_s(m), Definition 1.1), gives

S_k(n) ~ (√k)^{k(k−1)/2} · (1/k!) · n^{−k(k−1)/4} · k^n · Γ(3/2)^{−k} · ∏_{j=1..k} Γ(1 + j/2).

The 2010 paper corrects Corollary 4.4 only for d > 1 and states that the d = 1 formula is unchanged and
agrees with (F.4.5.1) of the 1981 paper.

Regev's constant equals Kotesovec's. By Γ(1 + x) = xΓ(x),
∏_{j=1..k} Γ(1 + j/2) = ∏_{j=1..k} (j/2) Γ(j/2) = (k!/2^k) ∏_{j=1..k} Γ(j/2),
and Γ(3/2) = √π/2 gives Γ(3/2)^{−k} = 2^k π^{−k/2}. The factors k! and 2^k cancel, and
(√k)^{k(k−1)/2} n^{−k(k−1)/4} = (k/n)^{k(k−1)/4}, so

S_k(n) ~ k^n π^{−k/2} (k/n)^{k(k−1)/4} ∏_{j=1..k} Γ(j/2),

which is the conjectured formula. For k = 10, ∏_{j=1..10} Γ(j/2) = (42525/32) π^{5/2}, which gives the
entry's %F line a(n) ~ 42525/32 · 10^{n+45/2} / (π^{5/2} n^{45/2}).

**Evidence.**
- `certificate/check.py` (about 65 s): Regev's constant, Kotesovec's constant and the %F constant agree to 40
  digits for k = 10 and k = 12; exact a(n) for n ≤ 400 from Gessel's Bessel determinant (checked against the
  hook-length sum for n ≤ 24 and the printed terms); a(n) divided by the asymptotic formula is 0.066 at
  n = 100 and 0.49 at n = 400 (slow approach, roughly like (n/(n+13))^{45/2}), and polynomial extrapolation of
  its logarithm in 1/n gives the limit 1 − 4·10^{−8} (k = 10) and 1 − 6·10^{−7} (k = 12).
- No Lean file: the statement is an asymptotic over all n.
- Outside Lean: Regev 1981 Corollary 4.4 (via arXiv:1004.4476 Theorem 3.5).

**Review level.** `rechecked`. Theorem 3.5 of arXiv:1004.4476 read in the source (v2); the 1981 paper itself
was not accessible (publisher returns 403), so Corollary 4.4 is taken from the 2010 restatement. The constant
reduction is re-derived above and checked numerically.

**Prior art.** Checked 2026-11-05: the entry does not cite Regev and still states the formula as a
conjecture. Not in google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/212916.lean`).

# OEIS A229068: standard Young tableaux of height ≤ 12, a(n) ~ 12^n π^(−6) (12/n)^33 ∏ Γ(j/2)

**Source.** OEIS [A229068](https://oeis.org/A229068) (offset 0): number of standard Young tableaux with n
cells and at most 12 rows. Conjecture (V. Kotesovec, Sep 2013): "generally (for tableaux with height <= k),
a(n) ~ k^n/Pi^(k/2) * (k/n)^(k*(k-1)/4) * Product_{j=1..k} Gamma(j/2); set k=12 for this sequence."
(OEIS text, CC BY-SA 4.0; revision #18.) The same general conjecture is in A212916 (k = 10).

**Result.** True for every k ≥ 1, by a theorem of Regev (1981).

**Argument.** Identical to [`../A212916/README.md`](../A212916/README.md): A. Regev, Adv. Math. 41 (1981)
115–136, Corollary 4.4, restated as Theorem 3.5 of arXiv:1004.4476, gives
S_k(n) ~ (√k)^{k(k−1)/2} (1/k!) n^{−k(k−1)/4} k^n Γ(3/2)^{−k} ∏_{j=1..k} Γ(1 + j/2) for the number S_k(n)
of standard Young tableaux with n cells and at most k rows. With
∏_{j=1..k} Γ(1 + j/2) = (k!/2^k) ∏_{j=1..k} Γ(j/2) and Γ(3/2)^{−k} = 2^k π^{−k/2} this is
k^n π^{−k/2} (k/n)^{k(k−1)/4} ∏_{j=1..k} Γ(j/2). For k = 12, ∏_{j=1..12} Γ(j/2) = (602791875/128) π^3,
which gives the entry's %F line a(n) ~ 602791875/128 · 12^{n+33} / (π^3 n^33).

**Evidence.**
- `certificate/check.py` (same script as A212916, about 65 s): the three constants agree to 40 digits for
  k = 10 and k = 12; exact a(n) for n ≤ 400 match the printed terms and the hook-length sum for n ≤ 24; for
  k = 12 the ratio a(n)/asymptotic is 0.0041 at n = 100 and 0.23 at n = 400, and extrapolation of its
  logarithm in 1/n gives the limit 1 − 6·10^{−7}.
- No Lean file: the statement is an asymptotic over all n.
- Outside Lean: Regev 1981 Corollary 4.4 (via arXiv:1004.4476 Theorem 3.5).

**Review level.** `rechecked` (Theorem 3.5 read in arXiv:1004.4476 v2; the 1981 paper was not accessible).

**Prior art.** Checked 2026-11-05: the entry does not cite Regev and still states the formula as a
conjecture. Not in google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/229068.lean`).

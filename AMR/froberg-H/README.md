# Fröberg–Lundqvist–Oneto–Shapiro Problem H: T_{n,2,2} = S/(x_1², …, x_n²)² has the WLP for every n

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and from the other
pockets*, Arnold Math. J. 4 (2018), §2.3, Problem H (paraphrased): when do T_{n,d,k} = S/(x_1^d, …, x_n^d)^k have
the WLP and the SLP? The text recalls that T_{n,2,2} has the WLP for odd n (Boij–Fröberg–Lundqvist, J. Algebra 495
(2018), Theorem 22) and that this is believed for even n; the BFL proof does not apply there.

**Reading.** S = C[x_1, …, x_n] (characteristic 0, any field of characteristic 0 or > 2 works for the new step),
WLP with respect to ℓ = x_1 + … + x_n (for monomial algebras the WLP holds iff it holds for this ℓ).

**Result.** Partial answer to Problem H (the example it names): T_{n,2,2} has the WLP for every n. New for
even n. The general classification of WLP/SLP for T_{n,d,k} stays open.

**Argument.** BFL's proof of Theorem 22 works verbatim for even n = 2k in every degree except the map
×ℓ: R_{k+1} → R_{k+2} (their closing remark). We prove that this map is injective
(dim R_{k+1} < dim R_{k+2}; dimension check below).

Basis of R_t: x_S (S ⊂ [n] squarefree, |S| = t), x_i² x_T (i ∉ T, |T| = t−2), x_i³ x_R (i ∉ R, |R| = t−3);
x_i²x_j² = x_i⁴ = 0. Write U (up) and D (down) for the Boolean-lattice maps U f(S) = Σ_{x∈S} f(S∖x).
Multiplying v = Σβ(S)x_S + Σγ(i,T)x_i²x_T + Σδ(i,R)x_i³x_R ∈ R_{k+1} by ℓ and reading coefficients:
(i) Uβ = 0 (squarefree part, level k+1 → k+2 on [2k]);
(ii) link_i β + Uγ_i = 0 for every i, where link_i β(T) = β(T ∪ i) on k-subsets of [2k]∖i;
(iii) γ_i + Uδ_i = 0.
So ℓv = 0 iff β ∈ ker U and link_i β = U²δ_i for all i; U² from level k−2 to k on 2k−1 points is injective, so
v = 0 iff β = 0. Thus injectivity ⇔ Φ: ker U → ⊕_i Fun_k([2k]∖i)/Im U², β ↦ (link_i β mod Im U²)_i, is injective.
By the sl₂ (Specht) decomposition of the Boolean lattice, ker U at level k+1 on [2k] is the irreducible
S_{2k}-module S^{(k+1,k−1)}, spanned by β = U²v with v = Π_{r<k}(e_{a_r} − e_{b_r}) (k−1 disjoint pairs, two
further points c, d). Φ is S_{2k}-equivariant, so by Schur it is injective or zero. It is not zero:
Im U² = (ker D²)^⊥, and w = Uv' with v' = Π_r(e_{a_r} − e_{b_r}) on [2k]∖c satisfies Dv' = 0 and DU − UD = 1 at
level k−1 on 2k−1 points, so D²w = Dv' = 0; and ⟨link_c β, w⟩ = Σ_T β(T∪{c,d})·w(T∪{d}) = Σ_T 2·sign(T)² = 2^k,
the sum over the 2^{k−1} transversals T of the pairs (sets T ∪ {y} with y a partner of an element of T give
w = 0 by cancellation). Hence Φ ≠ 0, Φ is injective, and ×ℓ: R_{k+1} → R_{k+2} is injective.

Dimension check: dim R_t = C(2k,t) + 2k·C(2k,t−2) (the x_i²-, x_i³-monomials form n copies of the Boolean level
t−2 on n points, as in BFL), and dim R_{k+2} − dim R_{k+1} = C(2k,k)/(k+1)·(2k − 3k/(k+2)) > 0.

**Evidence.**
- [`certificate/wlp.py`](certificate/wlp.py): rank of ×ℓ in every degree over GF(32749) (maximal rank mod p
  implies maximal rank over Q): WLP for T_{n,2,2}, n = 3..9 (calibrates BFL's odd case).
  [`certificate/wlp_one.py`](certificate/wlp_one.py): n = 10, degree 6 → 7: rank 2310 = dim R_6 (2 min).
- [`certificate/pairing.py`](certificate/pairing.py): checks Uβ = 0, D²w = 0 and ⟨link_c β, w⟩ = 2^k for k = 1..7.
- Lean: [`froberg_H_mathlib.lean`](froberg_H_mathlib.lean) (Mathlib, checked with `tools/leancheck-mathlib.sh`,
  axioms propext, Classical.choice, Quot.sound). `froberg_H_mul_ell_injective`: for #σ = 2k, a form p of degree
  k+1 in ℂ[x_σ] with ℓp ∈ (x_1², …, x_n²)² lies in that ideal, i.e. ×ℓ: R_{k+1} → R_{k+2} is injective;
  `froberg_H_even` is the case σ = Fin (2k). The Lean proof avoids Specht modules. It uses only adjointness of
  U and D and the commutator DU − UD = #(G∖S) − #S on a set S: on [2k]∖i, link_i β ∈ Im U² ⊆ (ker U)^⊥ = Im D
  (ker U ⊆ ker D² at level k on 2k−1 points), and writing link_i β = D g gives 3‖link_i β‖² ≤ ‖U link_i β‖² = ‖del_i β‖²
  (del_i β = β on sets avoiding i, using Uβ = 0). Summing over i gives 3(k+1)‖β‖² ≤ (k−1)‖β‖², so β = 0, and
  then γ = δ = 0 because U is injective below the middle.
- Outside Lean: BFL Theorem 22's proof for all other degrees (and odd n), which with the Lean theorem gives the
  WLP of T_{n,2,2} for every n; the rank computations above (Python).

**Review level.** `lean-proof` for the new step (×ℓ: R_{k+1} → R_{k+2} injective for n = 2k); BFL Theorem 22
for the other degrees is cited. Independent rank computations for n ≤ 10 and the pairing for k ≤ 7 agree.

**Prior art.** Checked 2026-11-07: BFL (arXiv 1612.00411, Theorem 22 and the closing remark), web searches for
WLP of (x_1², …, x_n²)² with n even (Booth–Singh–Vraciu 2024/25 and Migliore–Miró-Roig–Nagel 2012 concern powers
of general linear forms, not this ring), formal-conjectures (nothing). No proof of the even case found.

# OEIS A059970: nim-factorials of 2^n - 1 and 2^n + 2^(n-1) - 1

**Source.** [A059970](https://oeis.org/A059970) (John W. Layman, 2001): nim-factorials, a(1) = 1, a(n) = n ⊗ a(n-1)
(⊗ nim multiplication). "Conjectures: (1) Nim-Factorial(2^n-1)=1 (verified for n=1,2,3,...,16). (2)
Nim-Factorial(2^n+2^(n-1)-1)=2 (verified for n=1,2,3,...,15)." (OEIS text, revision #19 of Mar 24 2025, checked
2026-11-06.)

**Result.** Both are true for every n >= 1.

**Argument.** Standard facts (Conway, *On Numbers and Games*, ch. 6; Lenstra, "Nim multiplication"): F_k = [0, 2^(2^k))
is a subfield of the nimbers of size q_k = 2^(2^k); x_k = 2^(2^k) satisfies x_k ⊗ x_k = x_k ⊕ α_k with
α_k = 2^(2^k - 1) = x_0 ⊗ ... ⊗ x_(k-1) ∈ F_k; and a ⊕ (b ⊗ x_k) = a + b·2^(2^k) for a, b ∈ F_k, so
[0, 2^(2^k + j)) = F_k ⊕ [0, 2^j) ⊗ x_k. The Frobenius t ↦ t^(q_k) of F_(k+1) over F_k maps x_k to the other root
x_k ⊕ 1, so x_k^(q_k) ⊕ x_k = 1. For W ⊆ F_k and b ∈ F_k, b ≠ 0: Π_{a∈F_k} (a ⊕ b x_k) = b^(q_k) Π_c (x_k ⊕ c) =
b (x_k^(q_k) ⊕ x_k) = b.
1. *Claim (1).* Let P(V) be the nim product of the nonzero elements of V. For V = F_k ⊕ W x_k the elements with b = 0
   give P(F_k) = 1 (Wilson in a field of characteristic 2) and the rest give Π_{b∈W, b≠0} b, so P(V) = P(W). Hence
   P([0, 2^(2^k + j))) = P([0, 2^j)) and by induction P([0, 2^n)) = 1 = a(2^n - 1).
2. *Claim (2).* a(2^n + 2^(n-1) - 1) = P([0, 2^n)) ⊗ y(n) with y(n) = Π_{c < 2^(n-1)} (2^n ⊕ c). For n = 2^k + j with
   1 <= j < 2^k, the same computation gives y(n) = y(j). For n = 2^k (k >= 1) write F' = F_(k-1), x' = x_(k-1),
   m = 2^(k-1), W = [0, 2^(m-1)); then y(2^k) = Π_{w∈W} (s ⊕ w) = L_W(s) with s = x_k^(2^m) ⊕ x_k, while
   y(2^(k-1)) = L_W(x'), where L_W(t) = Π_{w∈W}(t ⊕ w) is additive. Since x_k^(2^l) = x_k ⊕ Σ_{i<l} α_k^(2^i) and
   α_k = x' ⊗ α', with α' = α_(k-1): s = x' ⊗ Tr(α') ⊕ e_2, where Tr(α') = Σ_{l<m} α'^(2^l) = 1 (t^2 + t + α' is
   irreducible over F') and e_2 = Σ_{i<l<m} α'^(2^i + 2^l) is fixed by Frobenius, so e_2 ∈ {0, 1} ⊆ W (k >= 2; for
   k = 1, e_2 = 0). Hence y(2^k) = y(2^(k-1)) = ... = y(1) = 2 and a(2^n + 2^(n-1) - 1) = 2.

**Evidence.**
- [`certificate/verify.py`](certificate/verify.py): nim factorials computed directly up to 2^21 - 1: claim (1) for
  n <= 21, claim (2) for n <= 20, and y(n) = 2 for n <= 18. [`certificate/nim.py`](certificate/nim.py): the nim
  product reproduces the entry's data, and s = x_k^(2^m) ⊕ x_k ⊕ x_(k-1) ∈ {0, 1} for k <= 5.
- Lean: none. Mathlib at the pinned revision has no nimbers. A Lean proof needs nim multiplication on ℕ and
  Conway's nim-field theorem (On Numbers and Games, ch. 6): [0, 2^(2^k)) with nim sum and product is the field
  GF(2^(2^k)), with x_k ⊗ x_k = x_k ⊕ α_k and a ⊕ (b ⊗ x_k) = a + b·2^(2^k). That theorem is the substantial missing
  piece; it was not attempted in the 2026-11-08 Lean pass (time box spent on A002093, A230496, A192062).
- Outside Lean: the whole argument, including the standard structure of the nim field.

**Review level.** `rechecked` (argument written here; its intermediate identities checked numerically).

**Prior art.** Checked 2026-11-06: the entry still lists both as conjectures; claim (1) for n a power of 2 is
Wilson's theorem in GF(2^(2^k)) (noted in the scan record); no proof of the general cases found by web search. Not in
google-deepmind/formal-conjectures (clone of 2026-11-06) or otoi-lab/oeis-lean-proofs (clone of 2026-10-13).

# OEIS A166102, A166103: odd k with k ∤ Σ{i ≤ k : J(i,k) = 1} are exactly 3·m², m ∈ A166104

**Source.** [A166102](https://oeis.org/A166102) (Antti Karttunen, 2009): odd numbers k such that A166100((k−1)/2)/k is
not an integer, where A166100(n) is the sum of those i ≤ 2n+1 with Jacobi symbol J(i, 2n+1) = +1. Comment:
"Conjecture: a(n) = 3*A166103(n). (Checked for terms a(1)-a(92).)" [A166103](https://oeis.org/A166103): squares of
[A166104](https://oeis.org/A166104) (numbers whose prime factors are all ≡ 3 or 5 mod 6); comment "Conjecture:
a(n)=A166102(n)/3." (OEIS text, CC BY-SA 4.0, A166102 revision #7 of Sep 16 2018, checked 2026-11-06.)

**Reading.** S(k) = Σ_{1≤i≤k, J(i,k)=1} i for odd k. The conjecture says: k ∤ S(k) iff k = 3m² with m odd and every
prime factor of m equal to 3 or ≡ 5 (mod 6); both sequences are increasing, so this set equality is the claim.

**Result.** True.

**Argument.** Let R = {i ≤ k : J(i,k) = 1}; J(·,k) is a multiplicative function of i mod k.
1. If J(u,k) = 1 then i ↦ ui permutes R mod k, so uS ≡ S (mod k). With u = 4: k | 3S. So k | S when 3 ∤ k, and in
   general k | S as soon as some u with J(u,k) = 1 has u ≡ 2 (mod 3) (then (u−1)S ≡ 0 and 3S ≡ 0 with
   gcd(u−1, 3) = 1).
2. Let 3 | k, k = 3^e N', 3 ∤ N'. If e is even, u ≡ 2 (mod 3), u ≡ 1 (mod N') gives J(u,k) = J(u,N') = 1. If e is
   odd and N' is not a square, pick a prime p with odd exponent in N', v a non-residue mod p, v ≡ 1 mod the rest
   of N' (so J(v, N') = −1), and u ≡ 2 (mod 3), u ≡ v (mod N'): J(u,k) = J(u,3)·J(u,N') = (−1)(−1) = 1. So k | S
   unless k = 3^e n² with e odd, 3 ∤ n, i.e. k = 3m².
3. k = 3m², m = 3^a n: J(i,k) = J(i,3)·J(i,m)², so R = {i : i ≡ 1 (mod 3), gcd(i,n) = 1}, a condition periodic
   mod M = 3n. With k = M·B, B = 3^{2a}·n odd, splitting [0,k) into B blocks of length M gives
   S(k) = B·S_M + |R_M|·M·B(B−1)/2 with S_M, |R_M| the sum and size of R in [0, M). So S(k)/k = S_M/M + integer.
   Multiplying by 4 shows n | S_M; every element of R_M is ≡ 1 (mod 3), so S_M ≡ |R_M| = φ(n) (mod 3) (the shift
   i ↦ i + n spreads the units mod n evenly over the three classes mod 3). Hence k | S iff 3 | φ(n) iff n has a
   prime factor ≡ 1 (mod 3).
4. So k ∤ S(k) iff k = 3m² with every prime factor of m equal to 3 or ≡ 2 (mod 3), i.e. (m odd) ≡ 5 (mod 6):
   k = 3·A166104(j)² = 3·A166103(j). Explicitly, for k = 3^e N (e odd, N = n²):
   S(k)/k = (3^e φ(N) − Π_{p|N}(1 − (p/3)))/6.

**Evidence.**
- Lean (Mathlib): [`A166103_mathlib.lean`](A166103_mathlib.lean). S(k) is defined as in A166100 (Finset sum over
  `Icc 1 k` with Mathlib's `jacobiSym`). Main theorem `A166102_iff k (Odd k) : ¬ k ∣ S k ↔ ∃ m, k = 3 * m ^ 2 ∧
  ∀ p, p.Prime → p ∣ m → p = 3 ∨ p % 6 = 5`. Route: step 1 `mul_invariant_gen`, `dvd_three_S`, `dvd_S_of_witness`;
  step 2 `witness_even`, `exists_jac_neg_one`, `witness_nonsq`; step 3 `jac_cond`, `block_sum`, `n_dvd_SP`,
  `SP_mod_three`, `card_cond`, `three_dvd_totient`, `square_case`. Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): with the A166100 b-file (k ≤ 262143) the 75 values of k with
  k ∤ S(k) are exactly 3m², m ∈ A166104; the closed form of step 4 holds for every k = 3^e n² in range; S(k)
  recomputed from Jacobi symbols for k < 400; the A166102 b-file (92 terms, [`certificate/b166102.txt`](certificate/b166102.txt))
  equals 3·A166104².
- Outside Lean: none beyond reading the definitions (the closed form of step 4 is not used by the Lean proof).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Both entries state the conjecture (checked to 92 terms); no proof found (web
search). The tools (characters permuting residue sets, CRT) are standard. Not in google-deepmind/formal-conjectures
or otoi-lab/oeis-lean-proofs.

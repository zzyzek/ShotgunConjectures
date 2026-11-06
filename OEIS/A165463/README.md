# OEIS A165463, A165462, A165460: Jacobi-bridge heights at the 1/3 and 1/2 points

**Source.** Antti Karttunen, Oct 2009 (OEIS text, CC BY-SA 4.0, checked 2026-11-06):
- [A165460](https://oeis.org/A165460)(n) = Sum_{i=0..4n+2} J(i, 12n+7) (J = Jacobi symbol). "Conjecture: a(2n) =
  2*A165605(2n) and a(2n+1) = (2/3)*A165605(2n+1)", where [A165605](https://oeis.org/A165605)(n) =
  [A165601](https://oeis.org/A165601)(3n+1) and A165601(n) = Sum_{i=0..2n+1} J(i, 4n+3).
- [A165462](https://oeis.org/A165462)(n) = (A165463(n) - 3)/4. "Conjecture: These are all those terms of A165602
  which = 1 modulo 3." ([A165602](https://oeis.org/A165602) = positions of zeros of A165601.)
- [A165463](https://oeis.org/A165463): numbers 12n+7 with A165460(n) = 0. "Conjecture: a subset of A165603."
  ([A165603](https://oeis.org/A165603) = numbers 4n+3 whose A165601 value is 0.)

**Result.** All three conjectures are true. With m = 12n+7, B = Sum_{i <= (m-1)/3} J(i, m) and
A = Sum_{i <= (m-1)/2} J(i, m): B = 2A if m = 7 (mod 24) (n even) and 3B = 2A if m = 19 (mod 24) (n odd). So
B = 0 iff A = 0, which gives A165462 and A165463.

**Argument.** Fix m = 7 (mod 12) and chi(i) = J(i, m): completely multiplicative, periodic mod m, chi(0) = 0, and
chi(m - i) = -chi(i) since m = 3 (mod 4). Let T = Sum_{0<=i<m} i chi(i).
1. For k coprime to m, i -> k i mod m permutes [0, m), and k i = (k i mod m) + m floor(k i/m). Multiplying T by
   k chi(k) and reindexing gives k chi(k) T = T + m chi(k) Sum_{i<m} floor(k i/m) chi(i).
2. Reflection i -> m - i gives Sum_{i<m} chi(i) = 0, Sum_{2i>m} chi(i) = -A and Sum_{3i>2m} chi(i) = -B. Hence
   Sum floor(2i/m) chi(i) = -A and Sum floor(3i/m) chi(i) = Sum_{3i>m} chi + Sum_{3i>2m} chi = (0 - B) + (-B) = -2B.
3. chi(3) = -J(m, 3) = -1 (reciprocity, both 3 mod 4; m = 1 mod 3), so k = 3 gives -4T = 2mB. chi(2) = 1 if
   m = 7 (mod 8) and -1 if m = 3 (mod 8); k = 2 gives T = -mA, respectively 3T = -mA. Eliminating T: B = 2A,
   respectively 3B = 2A. m = 12n+7 is 7 mod 8 iff n is even.

**Evidence.**
- Lean (Mathlib): [`A165463_mathlib.lean`](A165463_mathlib.lean), namespace `JacobiBridge`. `S m N = ∑ i ∈ range
  (N+1), jacobiSym i m`; `A165601`, `A165605`, `A165460` as in the OEIS names. Main theorems
  `A165460_conjecture : A165460 (2n) = 2 * A165605 (2n) ∧ 3 * A165460 (2n+1) = 2 * A165605 (2n+1)`,
  `A165462_conjecture : (∃ n, k = 3n+1 ∧ A165460 n = 0) ↔ (A165601 k = 0 ∧ k % 3 = 1)` (the left side is
  membership in A165462 = (A165463 - 3)/4), `A165463_subset`. Route: `mult` (step 1, via `sum_perm`), `reflect`,
  `D2`, `D3` (step 2), `chi_two`, `chi_three`, `key` (step 3). Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py) ([`check.out`](certificate/check.out)): both identities for
  n < 1500; the first terms of A165460, A165605, A165462, A165463 match the OEIS data.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entries list the claims as conjectures with no proof. For a prime modulus
p = 3 (mod 4) the evaluations (2 - chi(2)) h(-p) and (3 - chi(3)) h(-p)/2 of these partial sums by the class
number are classical (Dirichlet; see B. C. Berndt, "Classical theorems on quadratic residues", Enseign. Math.
1976), and they imply the relation for prime m. The Jacobi-symbol case for composite m by the elementary
reindexing argument above was not found in print. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.

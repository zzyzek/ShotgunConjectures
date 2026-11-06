# OEIS A166273, A166271, A166270, A166269, A166268: Jacobi-bridge heights at m/6, m/3, m/2 for m = 12n+7

**Source.** OEIS bisections by A. Karttunen (Oct 2009), each with a comment "Conjecture: ...":
[A166273](https://oeis.org/A166273) a(n) = −3·A166269(n); [A166271](https://oeis.org/A166271) a(n) = −2·A166269(n);
[A166269](https://oeis.org/A166269) a(n) = −(1/2)·A166271(n); [A166270](https://oeis.org/A166270) a(n) = 2·A166268(n);
[A166268](https://oeis.org/A166268) a(n) = A166270(n)/2 and also A165605(A005843(n)). (OEIS text, CC BY-SA 4.0,
checked 2026-11-06.)

**Reading.** For m = 12n+7 and J the Jacobi symbol: A165605(n) = A165601(3n+1) = sum_{i=0..6n+3} J(i, m),
A165460(n) = sum_{i=0..4n+2} J(i, m), A166050(n) = sum_{i=0..2n+1} J(i, m), i.e. H(x) = sum of J(i, m) over
0 ≤ i < x·m at x = 1/2, 1/3, 1/6. A166273, A166271, A166269 are the odd bisections (m ≡ 19 mod 24) of A165605,
A165460, A166050; A166270, A166268 the even bisections (m ≡ 7 mod 24) of A165460, A166050.

**Result.** All true: for m ≡ 7 (mod 24), H(1/3) = 2H(1/6) and H(1/2) = H(1/6); for m ≡ 19 (mod 24),
H(1/2) = −3H(1/6) and H(1/3) = −2H(1/6). This holds for every m in these classes, squarefree or not.

**Argument.** Let χ = J(·, m): m-periodic, completely multiplicative, χ(−1) = −1 (m ≡ 3 mod 4), χ(3) = −1
(reciprocity, m ≡ 3 mod 4 and m ≡ 1 mod 3), χ(2) = +1 for m ≡ 7 (mod 8), −1 for m ≡ 3 (mod 8). Write
m = 6q+1. The integers 1..m−1 form six blocks B_j = {jq+1, ..., (j+1)q} (j = 0..5); let a(j, r) be the sum of
χ(n) over n ∈ B_j with n ≡ r (mod 6). Then H(1/6) = sum_r a(0, r), H(1/3) adds block 1, H(1/2) adds block 2.
Three families of linear relations hold:
- reflection n ↦ m − n: a(5−j, 1−r mod 6) = −a(j, r);
- doubling n ↦ 2n (j ≤ 2) or 2n − m (j ≥ 3): χ(2)·(a(j, r) + a(j, r+3)) equals a(2j, s) + a(2j+1, s)
  (indices mod 6), s = 2r − t (mod 6), t = ⌊j/3⌋;
- tripling n ↦ 3n − t m, t = ⌊j/2⌋: χ(3)·(a(j, r) + a(j, r+2) + a(j, r+4)) equals the sum of a(3j−6t+i, s),
  i = 0, 1, 2, s = 3r − t (mod 6).
With (χ(2), χ(3)) = (1, −1) or (−1, −1), these 66 relations imply the stated identities (a linear combination of
12–16 of them; found by Gaussian elimination, checked by `linarith` in Lean). No class-number formula or
primitivity of χ is used.

**Evidence.**
- Lean (Mathlib): [`A166273_mathlib.lean`](A166273_mathlib.lean). The sequences are defined literally with
  Mathlib's `jacobiSym` (`A165601`, `A165605`, `A165460`, `A166050` and the five bisections). Main theorems
  `A166273_main`, `A166271_main`, `A166269_main` (2·a(n) = −A166271(n)), `A166270_main`, `A166268_main`, via
  `A166273_jacobi` and the character-free `A166273_abstract` (relations `A166273_refl`, `A166273_dbl0`,
  `A166273_dbl1`, `A166273_tpl`). `A166273_data` checks the first terms by `decide`. Axioms: propext,
  Classical.choice, Quot.sound.
- [`certificate/check_jacobi.py`](certificate/check_jacobi.py): brute force for n < 6000;
  [`certificate/linear_relations.py`](certificate/linear_relations.py): rank test that the relations imply the
  identities.
- Outside Lean: nothing beyond reading the definitions (the bisection indexing, A005408/A005843).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. For prime m (primitive χ) these are instances of classical formulas for
partial sums of an odd real character at k/2, k/3, k/6 in terms of the class number (B. C. Berndt, "Classical
theorems on quadratic residues", Enseign. Math. 22 (1976); W. Johnson and K. Mitchell, Pacific J. Math. 1977;
R. H. Hudson and K. S. Williams, Math. Comp. 39 (1982)); the exact /6 formula was not read in those papers here.
The general Jacobi-symbol case (imprimitive χ, e.g. m = 175) and the elementary route are not found there. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones).

# OEIS A008683 (comment): a moved-corner divisibility matrix has determinant μ(n) and A074206(n) nonzero terms

**Source.** OEIS [A008683](https://oeis.org/A008683), comment by M. Granvik (Dec 08 2008): "Conjecture: Consider
the table A051731 and treat 1 as a divisor. Move the value in the lower right corner vertically to a divisor
position in the transpose of the table and you will find that the determinant is the Moebius function. The number
of permutation matrices that contribute to the Moebius function appears to be A074206." (OEIS text, CC BY-SA 4.0,
checked 2026-11-06.)

**Reading.** The wording admits two concrete matrices (n × n, n ≥ 2); both satisfy both claims.
1. A = A051731 truncated (A(i, k) = 1 iff k | i), with the 1 at (n, n) moved up its column to row 1, so column n
   becomes e_1.
2. The Redheffer matrix (R(i, j) = 1 iff j = 1 or i | j: the transpose of A051731 with 1 "treated as a divisor"
   in the first column) with the entry (n, n) set to 0; this is the matrix of the A008683 comment on A143104.
"Contributing permutation matrices" = permutations σ with all entries M(i, σ(i)) nonzero.

**Result.** True for both readings and every n ≥ 2: det = μ(n), and the number of contributing permutations is
H(n) = A074206(n), the number of ordered factorizations of n.

**Argument.**
- *Determinant, reading 1.* Expanding along column n, det A' = (−1)^(n+1) det N, N = A without row 1 and column n.
  A is unitriangular with inverse A^(−1)(i, k) = μ(i/k)[k | i] (Möbius inversion), and the cofactor formula
  gives μ(n) = A^(−1)(n, 1) = (−1)^(n+1) det N.
- *Determinant, reading 2.* det is linear in column n; removing e_n from column n subtracts the determinant of the
  (n−1) × (n−1) Redheffer matrix. By Redheffer's theorem (det of the k × k Redheffer matrix is the Mertens
  function M(k)), det = M(n) − M(n−1) = μ(n).
- *Count.* Reading 1: σ(1) = n is forced, and the remaining rows m = 2..n go injectively to columns 1..n−1 with
  σ(m) | m, so σ(m) ≤ m. Starting from n and following σ gives a strictly decreasing divisor chain
  n = c_0 > c_1 > ... > c_k = 1 (a value repeated would have two preimages); the rows off the chain are mapped
  among themselves with σ(m) ≤ m, which forces σ(m) = m. Chains correspond to ordered factorizations
  n = (c_0/c_1)(c_1/c_2)...(c_(k−1)/c_k). Reading 2: row n can only use column 1 (its only other candidate is
  (n, n) = 0), and rows 1..n−1 go to columns 2..n with i | σ(i); the same chain argument applies upward from 1.
  (Reading 1 is D. Callan's 2005 comment in A074206: H(n) is the permanent of N.)

**Evidence.**
- Lean (core): [`A008683b.lean`](A008683b.lean). `A008683b_check`: for 2 ≤ n ≤ 10 and both matrices, the
  Leibniz determinant equals μ(n) and the number of contributing permutations equals H(n) (`decide +kernel`,
  no axioms); `A008683b_tables` checks the μ and H implementations against the OEIS data.
- [`certificate/check.py`](certificate/check.py) (output `certificate/out.txt`): the same for n ≤ 16.
- Outside Lean: the general-n argument above (Möbius inversion / Redheffer's theorem; the chain bijection).

**Review level.** `lean-witness` (finite cases); the general statement rests on the argument above.

**Prior art.** Checked 2026-11-06: the determinant part is classical (Möbius inversion of the zeta matrix;
R. M. Redheffer, "Eine explizit lösbare Optimierungsaufgabe", Internat. Schriftenreihe Numer. Math. 36 (1977),
for det = M(n)); the count for reading 1 is D. Callan's comment in A074206 (2005). The combination as stated was
not found written up. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

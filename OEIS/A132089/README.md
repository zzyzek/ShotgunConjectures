# OEIS A132089: the first column of L^(m+1) is the row-sum sequence of L^m (L = Losanitsch's triangle)

**Source.** OEIS [A132089](https://oeis.org/A132089), triangle T = L^2 where L is Losanitsch's triangle
A034851 (G. McGarvey, Oct 2007). Comment: "Conjectures: (1) The first column equals the row sums of
Losanitsch's triangle (which equals A005418). (2) Let L^n denote the n-th power of Losanitsch's triangle. Then
the first column of L^(n+1) equals the row sums of L^n." (OEIS text, CC BY-SA 4.0, revision #2 of Mar 30 2012,
still conjecture on 2026-11-06.)

**Reading.** L(n, k) = (C(n, k) + C(n mod 2, k mod 2) C(⌊n/2⌋, ⌊k/2⌋))/2, rows and columns from 0 (the entry's
PARI program). L is lower triangular, so powers are well defined as infinite matrices and agree with the
entry's truncated s × s computation.

**Result.** True, both parts; (1) is (2) with power 1. The identification "row sums of L = A005418" in (1) is
the known name of A005418 (Losanitsch).

**Argument.** L(j, 0) = (1 + 1·1)/2 = 1 for every j. So L^(m+1)(n, 0) = sum_j L^m(n, j) L(j, 0) =
sum_j L^m(n, j), the n-th row sum of L^m.

**Evidence.**
- Lean (core): [`A132089.lean`](A132089.lean). `A132089_main`: for all m, n,
  `A132089_pow (m+1) n 0 = sum_{k ≤ n} A132089_pow m n k`; `A132089_pow_upper` (L^m lower triangular, so the
  finite sums are the matrix product); `A132089_data` (the 65 listed terms equal L^2, `decide`);
  `A132089_A005418` (row sums of L equal 2^(n-1) + 2^(⌊(n+1)/2⌋-1) = A005418(n+1) for 1 ≤ n ≤ 40, `decide`).
  Axioms: propext, Quot.sound.
- Outside Lean: the row-sum identity with A005418 for n > 40 (known: it is part of A005418's name; it follows
  from sum_k C(n, k) = 2^n and sum_k C(n mod 2, k mod 2) C(⌊n/2⌋, ⌊k/2⌋) = 2^⌈n/2⌉).

**Review level.** `lean-proof` (for the conjecture as stated; the parenthetical A005418 identification is the
known fact above).

**Prior art.** Checked 2026-11-06: OEIS A132089, A034851, A005418 entries; no write-up of the conjecture found
(it is immediate from L(j, 0) = 1). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

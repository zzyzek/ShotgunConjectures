# OEIS A221650: P(n,j,k) = [k | j] p(n-j) counts partitions with at least j/k parts k

**Source.** OEIS [A221650](https://oeis.org/A221650): tetrahedron P(n,j,k) = T(j,k) p(n-j), T(j,k) =
1 if k | j else 0. Conjecture 1: "P(n,j,k) is the number of partitions of n that contain at least
m parts of size k, where m = j/k, if k divides j otherwise P(n,j,k) = 0." Conjecture 2: "P(n,j,k) is
the number of parts that are the m-th part of size k in all partitions of n ..." (O. Omar, 2013;
OEIS text, CC BY-SA 4.0.)

**Result.** Both true.

**Argument.** Removing m copies of k from a partition of n with at least m parts equal to k is a
bijection onto the partitions of n - mk = n - j (inverse: add m copies of k). So the count is
p(n - j). Conjecture 2 counts, over all partitions of n, the parts that are the m-th occurrence of
k; each partition with at least m parts k contributes exactly one such part, so the count is the
same.

**Evidence.**
- `certificate/a221650.py`: enumeration for n ≤ 30, all k, m.
- Lean (Mathlib): [`A221650_mathlib.lean`](A221650_mathlib.lean), `A221650_main`: for 1 ≤ k ≤ j ≤ n, P(n,j,k) = [k | j]·p(n-j) equals the number of partitions of n (`Nat.Partition`) with at least j/k parts k, and the number of parts that are the (j/k)-th part of size k; P = 0 if k ∤ j. Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).

**Prior art.** Partly known (folklore). [OEIS A221650](https://oeis.org/A221650) (fetched 2026-11-04) still states both conjectures. The bijection (remove m copies of k) is textbook-level, and the column-sum version is in [A066633](https://oeis.org/A066633) (Arregui, 2002). Searched: entry, OEIS cross-reference search, edit history, A221649, A066633. Worth an OEIS comment. (Prior-art review 2026-11-04.)

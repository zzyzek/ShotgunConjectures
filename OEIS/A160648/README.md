# OEIS A160648: second differences of A160644 count partitions with three equal largest parts

**Source.** [A160648](https://oeis.org/A160648), offset 1: second differences of A160644, the even bisection of
A053445 (second differences of the partition numbers). Conjecture in the entry: "a(n) counts unrestricted
partitions of even numbers such that the three largest values match and that, after "222", no part is less than
three." Example: a(2) = 1 (222), a(5) = 2 (444, 3333), a(8) = 4 (666, 5553, 44433, 333333). (OEIS text checked
2026-11-08.)

**Reading.** a(n) = A160644(n) - 2 A160644(n-1) + A160644(n-2) with A160644(j) = A053445(2j) (j >= 0); this
reproduces the data. The example puts partition sizes at 2n + 2. The conjecture: for n >= 1, a(n) = c(2n+2) + [n = 2],
where c(m) counts partitions of m with all parts >= 3 whose largest part has multiplicity >= 3 (the three largest
parts equal); the extra 1 at n = 2 is the partition 222.

**Result.** True for every n >= 1.

**Argument.** Let q3(m) count partitions of m with all parts >= 3 (q3(0) = 1), and g_r(m) those with largest-part
multiplicity >= r (m >= 1).
1. p(m) - p(m-1) counts partitions of m without part 1, so A053445(j) = q2(j+2) - q2(j+1) (q2: parts >= 2), and
   a(n) = [x^(2n+2)] (1-x)(1-x^2)^2 Q2(x) = [x^(2n+2)] (1-x)(1-x^2) Q3(x), since (1-x^2) Q2 = Q3. So
   a(n) = q3(m) - q3(m-1) - q3(m-2) + q3(m-3) with m = 2n+2.
2. Lowering a unique largest part by 1 is a bijection from multiplicity-1 partitions of m onto nonempty
   partitions of m-1 with parts >= 3, except for (3) at m = 3. Hence g_2(m) = q3(m) - q3(m-1) - [m = 3].
3. Lowering both largest parts by 1 maps partitions with largest multiplicity exactly 2 bijectively onto
   partitions of m-2 counted by g_2, except for (3,3) at m = 6. Hence c(m) = g_3(m) = g_2(m) - g_2(m-2) - [m = 6]
   = q3(m) - q3(m-1) - q3(m-2) + q3(m-3) - [m = 3] + [m = 5] - [m = 6].
4. For even m = 2n+2 >= 4 this is a(n) - [n = 2].

**Evidence.**
- Lean (Mathlib): [`A160648_mathlib.lean`](A160648_mathlib.lean), theorem `A160648_conj`: for n >= 2,
  A160648 n = cc (2n+2) + [n = 2], with p(m) = card (Nat.Partition m), A053445, A160644, A160648 defined from p as
  in the entries, and cc m the number of partitions of m with parts >= 3 whose largest part has multiplicity >= 3.
  Steps 1-3 are formalised: `q_rec` (remove a part, via Nat.Partition.partitionWithPartEquiv), `E_eq` (lower the
  r largest parts, maps `dn`/`upm`), `E26` (the exception 3+3). Checked with tools/leancheck-mathlib.sh; axioms
  propext, Classical.choice, Quot.sound.
- certificate/check.py recomputes a(n) from the partition numbers and c(2n+2) from the generating function,
  equal for n <= 1200.
- Outside Lean: a(1) = 0 (the first data term, below the range n >= 2 of the Lean statement; c(4) = 0) and the
  reading that "three largest values match, after 222 no part less than three" means the set counted by cc plus 222.

**Review level.** Lean proof for all n >= 2; numerically checked to n = 1200.

**Prior art.** OEIS entry (still a conjecture), A053445 and A160644 comments, web search, google-deepmind/
formal-conjectures (no A160648 file), checked 2026-11-08. The bijections are standard (largest-part reduction).
The same argument gives the general form: second differences in steps of 1 of q_s count partitions with parts
>= s whose largest part has multiplicity >= 3, up to boundary terms.

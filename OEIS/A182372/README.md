# OEIS A182372: sets with perimeter n and two-sort partitions are equinumerous

**Source.** [A182372](https://oeis.org/A182372) (offset 0): "Number of distinct sets of nonnegative integers with
perimeter n", where the perimeter of S is the sum of the elements of S whose predecessor and successor are not both
in S. Comment: "Conjecture: number of partitions of n into two sorts of parts such that no two successive parts are
the same sort (as the order of sorts in a run of identical parts is immaterial, there can be at most two parts of
same size), see example. - _Joerg Arndt_, Jun 01 2013", and "The conjecture of Arndt [namely that a(n) = A227134(n)
+ A227135(n)] has been verified for n < 1200. - _Patrick Devlin_, Jul 02 2013". (OEIS text, revision #81 of Nov 05
2025, checked 2026-11-06.)

**Reading.** Sets are finite (an infinite tail {t, t+1, ...} would add only t to the perimeter, making every a(n)
infinite), and 0 always counts as a perimeter element since -1 is not in S. A two-sort partition is a list of
pairs (part, sort), parts ≥ 1, sorts in {0, 1}, listed in increasing lexicographic order with no repeated pair,
whose sorts alternate. This is how Arndt's example lists them (a(9) = 24: [1:0 1:1 7:0] is listed, [1:0 1:1 7:1] is
not), and it splits by first sort into A227134 (first sort 0) and A227135 (first sort 1). The empty partition is
counted once here and once in each of A227134, A227135; the empty set is counted in a(0) = 2.

**Result.** True: for every n ≥ 0, the number of nonempty finite sets S ⊆ ℕ with perimeter n equals the number
of two-sort partitions of n. Hence a(n) = (two-sort partitions of n) for n ≥ 1, a(0) = 2, and
a(n) = A227134(n) + A227135(n) for all n ≥ 0.

**Argument.** Let Y_m(n) count sequences 0 ≤ y_1 < y_2 ≤ y_3 < y_4 ≤ ... of length m and sum n (strict after
odd positions, weak after even ones). Its generating function is x^Q(m)/(x;x)_m with Q(m) = floor(m^2/4). Both
sides equal Σ_{m≥1} Y_m(n).

1. *Two-sort partitions.* In the lexicographic listing, equal neighbouring parts carry sorts (0, 1), so the list
   p_1 ≤ ... ≤ p_k is weakly increasing after a part of sort 0 and strictly increasing after a part of sort 1. If
   the first sort is 1, the list is strict after odd positions: it is a Y_k sequence with y_1 ≥ 1. If the first
   sort is 0, prepend y_1 = 0: (0, p_1, ..., p_k) is a Y_{k+1} sequence with y_1 = 0. Every Y_m sequence arises
   once, except (0) of length 1, which corresponds to the empty partition. So
   #(two-sort partitions of n) = Σ_{m≥1} Y_m(n) for every n ≥ 0.
2. *Sets, one shape at a time.* A nonempty set is a union of b ≥ 1 maximal runs; let L ⊆ {1..b} be the runs of
   length ≥ 2. Its perimeter elements are the run ends: k = b + |L| numbers e_1 < ... < e_k with Σ e = perimeter.
   The set is determined by (b, L, e), and e ranges over all sequences with e_{i+1} - e_i ≥ 1 inside a run and
   ≥ 2 between runs. Writing e by its first term and differences, the sets with shape (b, L) have generating
   function x^{E}/(x;x)_k (if 0 ∉ S, e_1 ≥ 1) and x^{E-k}/(x;x)_{k-1} (if 0 ∈ S, e_1 = 0), where
   E = k + C(k,2) + Σ_{j<b} (number of perimeter elements in runs j+1..b) = C(k+1,2) + C(b,2) + Σ_{t∈L} (t-1).
   Summing over L with |L| = l uses Σ_{|L|=l} x^{Σ(t-1)} = x^{C(l,2)} [b choose l]_x. After clearing
   denominators, "sets with b runs and 0 ∉ S have generating function x^{b^2}/(x;x)_{2b}" and "sets with b runs
   and 0 ∈ S have generating function x^{b(b-1)}/(x;x)_{2b-1}" become the two cases c = b and c = b - 1 of
3. *the q-identity* Σ_{l=0}^{b} x^{l(l+c)} [b choose l]_x / (x;x)_{c+l} = 1/(x;x)_{b+c} (b, c ≥ 0). Proof by
   induction on b: b = 0 is trivial; with [b choose l] = [b-1 choose l] + x^{b-l} [b-1 choose l-1] the sum splits
   into F(b-1, c) + x^{b+c} F(b-1, c+1) = 1/(x;x)_{b+c-1} + x^{b+c}/(x;x)_{b+c} = 1/(x;x)_{b+c}.
4. So the nonempty sets with perimeter n, split by m = 2b - [0 ∈ S], number Y_m(n); summing over m and comparing
   with step 1 proves the claim.

The statistic m = 2(number of runs) - [0 ∈ S] was found by a search over small linear combinations of set
statistics ([`certificate/statistic_search.py`](certificate/statistic_search.py)).

**Evidence.**
- [`certificate/check.py`](certificate/check.py): (a) brute force over all sets for n ≤ 16: the sets with perimeter
  n and m = 2b - [0 ∈ S] number exactly Y_m(n), and the total equals the brute-force count of two-sort partitions;
  (b) the q-identity of step 3 as a polynomial identity Σ_l x^{l(l+c)} [b,l] (x^{c+l+1};x)_{b-l} = 1 for
  b, c ≤ 12; (c) 1 + Σ_m x^Q(m)/(x;x)_m equals the b-file ([`certificate/b182372.txt`](certificate/b182372.txt))
  for n ≤ 200.
- Lean (Mathlib): [`A182372_mathlib.lean`](A182372_mathlib.lean) proves the q-identity of step 3 in ℤ[X],
  `qidentity b c : Σ_{l ≤ b} X^(l(l+c)) [b,l]_X (X^(c+l+1); X)_(b−l) = 1`, with the Gaussian binomials defined by
  q-Pascal (`gauss`) and the q-Pochhammer product `poch`; induction on b as in step 3; and the Gaussian-binomial
  subset sum of step 2, `subset_sum b l : Σ_{L ⊆ {0..b−1}, |L| = l} X^(Σ L) = X^(C(l,2)) [b,l]_X`. Check:
  `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound.
- Outside Lean: step 1 (the bijection of two-sort partitions with Y-sequences), the generating functions of run
  shapes in step 2, step 4, and the link of the generating functions to the OEIS definitions; checked numerically
  only.

**Review level.** `rechecked` (proof re-derived; step 3 Lean-checked, the other steps checked numerically).

**Prior art** (2026-11-06). OEIS entry, history, A227134 and A227135 (conjecture still open there; Hanna's g.f.s
for A227134/A227135/A182372 are stated without proof); web search (perimeter-of-integer-sets and fixed-perimeter
partition papers, J. Arndt's fxt demo output which calls it a conjecture); google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs: no file for A182372. No proof found. The q-identity in step 3 is a standard
Durfee-rectangle identity; the reduction to it is ours.

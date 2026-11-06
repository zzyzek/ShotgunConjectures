# OEIS A076072, A076070: a multiple of n can always be formed from the digits of the next n numbers

**Source.** [A076072](https://oeis.org/A076072) (largest) and [A076070](https://oeis.org/A076070) (smallest multiple of n
formed by using the digits of the next n numbers, or 0 if none), Amarnath Murthy, Oct 2002. Both: "Conjecture: No
entry is zero." "Next n numbers" means T(n-1)+1, ..., T(n) with T(n) = n(n+1)/2 (M. F. Hasler's comment). (OEIS
text, revisions #14 of Jan 17 2020 and #12 of Mar 18 2025, checked 2026-11-06.)

**Reading.** "Formed by using the digits": a permutation of the multiset of all decimal digits of the n numbers,
read as a decimal number without a leading zero (the entries' terms are of this form).

**Result.** True for every n >= 1: some arrangement of the digits is a multiple of n.

**Argument.** For n < 1200 by computer (below). Let n >= 1200, n = 2^a 5^b N' with gcd(N', 10) = 1, e = max(a, b),
and H = gcd(9, N')·Z/N', a cyclic group of order h = N'/gcd(9, N') <= n.
1. *Digit counts.* Among n consecutive integers each digit value occurs as units digit at least n/10 - 1 times, as
   tens digit at least n/10 - 10 times and as hundreds digit at least n/10 - 100 times (complete blocks of 10, 100,
   1000). So every digit value occurs at least 3n/10 - 111 times. Reserve e zeros and one digit 1. The pairs
   (0,1), (2,3), (4,5), (6,7), (8,9) then give at least 5(3n/10 - 111) - e - 1 >= n - 1 >= h - 1 disjoint pairs
   (v, v+1), because e <= log2 n and n >= 1200.
2. *Arrangement.* From the right: the e zeros; then h - 1 pairs at positions (e+2t, e+2t+1); then the other digits;
   the reserved 1 in front. Every such number is divisible by 2^a 5^b. Swapping the two digits of pair t changes
   the value by ±9·10^(e+2t), a generator of H in Z/N'.
3. *Subset sums.* If A ⊆ H and x generates H, then A ∪ (A + x) is larger than A unless A = H. So the h - 1 optional
   swaps reach V0 + H mod N', where V0 is the value with no swap.
4. *The residue mod 9.* Every arrangement is congruent mod 9 to the digit sum, hence to the sum of the n numbers,
   n(n^2 + 1)/2. If 3 | N' then 3 | n and 3 | n(n^2+1)/2; if 9 | N' then 9 | n(n^2+1)/2. So V0 ∈ H and some choice of
   swaps gives 0 mod N'. With step 2 the number is divisible by n, and its leading digit is 1.

**Evidence.**
- [`certificate/search.py`](certificate/search.py), log [`certificate/search.log`](certificate/search.log): for every
  n < 1200 a random search finds an arrangement (no leading zero) divisible by n; each hit is rechecked with exact
  integer arithmetic and digit-multiset comparison (at most 7.22 n shuffles per n; run 2026-11-06).
- [`certificate/construct.py`](certificate/construct.py): carries out steps 1-4 (pair counts, positions, the
  subset-sum choice) for n = 1200..1599 and eight larger n, and checks the resulting number exactly.
- Lean: none. Outside Lean: the whole argument and the computation.
- The b-file of A076070 (Sean A. Irvine, n <= 74) agrees that no entry is 0.

**Review level.** `rechecked` (argument written by this entry's author; construction executed for 408 values of n;
exhaustive computation for n < 1200).

**Prior art.** Checked 2026-11-06: both entries still say "Conjecture"; web search found no proof; not in
google-deepmind/formal-conjectures (clone of 2026-11-06) or otoi-lab/oeis-lean-proofs (clone of 2026-10-13).

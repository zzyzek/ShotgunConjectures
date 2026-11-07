# Guy UPINT B4 (Wall): members of an odd amicable pair are incongruent mod 4, checked on all known pairs

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section B4 (paraphrased): Charles Wall asks
whether the two members of every odd amicable pair are incongruent modulo 4.

**Result.** Partial; the question stays open.
1. (Reduction, classical ingredients.) For an amicable pair (m, n) with m odd, the following are equivalent:
   (a) n is odd and m ≡ n (mod 4); (b) σ(m) ≡ 2 (mod 4); (c) m = p^a k² with p prime, p ≡ a ≡ 1 (mod 4), p ∤ k
   (Euler form); (d) n is odd and of Euler form. So a counterexample is a pair of odd numbers of Euler form, both
   ≡ 1 (mod 4).
2. (Data.) No counterexample among the 5 697 688 odd pairs in S. Chernykh's list of all known amicable pairs
   (2023-01-01). The list is complete for pairs with smaller member below 10^20, which contain 1 975 654 odd pairs.
   In every one of the 5 697 688 odd pairs the members are incongruent mod 4, and neither member has Euler form.

**Argument.** (a)⇒(b): σ(m) = m + n ≡ 2 (mod 4). (b)⇒(a): σ(n) = σ(m) = m + n is ≡ 2 mod 4, so n is odd (m odd,
n even would make m + n odd), hence m ≡ n (mod 4). (b)⇔(c): for an odd prime q, σ(q^e) is odd iff e is even, so
v₂(σ(m)) = 1 forces exactly one prime p with odd exponent a; then σ(p^a) = (1 + p)(1 + p² + … + p^(a−1)), whose
second factor has parity (a+1)/2, and v₂ = 1 iff p ≡ 1 (mod 4) and a ≡ 1 (mod 4) (Euler's argument for odd perfect
numbers). (c)⇔(d): apply (b)⇔(c) to n, since σ(n) = σ(m).

**Evidence.**
- [`certificate/oddfilter.py`](certificate/oddfilter.py) streams the list
  (`7z x -so data/amicable/c2_filtered.7z | python3 -I oddfilter.py odd_pairs.txt`, see [DATA.md](../../DATA.md)),
  checks that each listed factorization multiplies out to the listed number, and for every pair with both
  members odd tests m mod 4 = n mod 4 and the Euler form of each member. Output:
  `pairs 10221707 odd 5697688 congruent 0 euler 0`. Run time about 4 minutes.
- Outside Lean: everything. The reduction is a paper argument (classical); the data check relies on the
  correctness and the stated completeness (below 10^20) of Chernykh's list; the σ-values of the listed pairs were
  not recomputed (the mod-4 test uses only the numbers themselves).

**Review level.** `rechecked` (reduction re-derived; data scanned here).

**Prior art.** Checked 2026-11-07: web search, erdosproblems.com, formal-conjectures (`Wikipedia/AmicableNumbers.lean`
has no mod-4 statement). No published check of Wall's question against the complete lists was found. The reduction to
Euler form is a direct transfer of Euler's odd-perfect-number argument.

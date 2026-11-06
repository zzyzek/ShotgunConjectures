# Guy, Unsolved Problems in Number Theory

R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004. Statements are paraphrased with the section number.

28 entries: 17 resolved by this project, 9 answered elsewhere, 0 disputed or partial.

Of the 17 resolutions: 15 proved in full in Lean, 1 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 1 on paper only (re-derived by a second reader; 0 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Resolved by this project

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A3.9](A3.9/) | disproved | the smallest prime with digit sum k does not always end in 99 | [full proof](A3.9/A3_9_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A19.2](A19.2/) | proved | infinitely many n with every n − 2^k squarefree | [full proof](A19.2/A19_2_mathlib.lean) | new | [density-bound](../methods/density-bound/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [B2.1](B2.1/) | proved | every n ≥ 2 is a sum of two deficient numbers | [full proof](B2.1/B2_1_mathlib.lean) | new | [density-bound](../methods/density-bound/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [B2.7](B2.7/) | disproved | a harmonic number with two harmonic seeds | [full proof](B2.7/B2_7_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [B2.8](B2.8/) | disproved | H(n) = 3p does not force a harmonic number to be arithmetic | [full proof](B2.8/B2_8_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [B10.3](B10.3/) | proved | Meeussen's numbers are not values of W(n) = n − d(n) − φ(n) + 1 | [full proof](B10.3/B10_3_mathlib.lean) | new | [modular-obstruction](../methods/modular-obstruction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [B16.6](B16.6/) | proved | 46 and 430 are the two smallest composite exceptions to the Ankeny–Artin–Chowla property | [full proof](B16.6/B16_6_mathlib.lean) | partly-known | [exact-arithmetic](../methods/exact-arithmetic/README.md), [units-pell](../methods/units-pell/README.md) |
| [B16.7](B16.7/) | trivial or misstated | every gap occurs between consecutive squarefree numbers | [full proof](B16.7/B16_7_mathlib.lean) | partly-known | [density-bound](../methods/density-bound/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [B36.6](B36.6/) | trivial or misstated | convergence of Σφ(n)/n^x and Σ(−1)^(n+1)φ(n)/n^x | [full proof](B36.6/B36_6_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md) |
| [B40.2](B40.2/) | disproved | totatives of large n need not contain a Pythagorean triple | [full proof](B40.2/B40_2.lean) | partly-known | [modular-obstruction](../methods/modular-obstruction/README.md) |
| [B40.3](B40.3/) | trivial or misstated | totatives of large n contain k-term arithmetic progressions | [full proof](B40.3/B40_3_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [B41.5](B41.5/) | proved | Finucane's lists for the iteration n → φ(n) + 1 are complete | [full proof](B41.5/B41_5_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md) |
| [D2.2](D2.2/) | disproved | x^n + y^n = n!·z^n has a solution with n = 3 | [full proof](D2.2/D2_2.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [E4.3](E4.3/) | disproved | Erdős's last question on primitive sets — the x²/6 guess is too small | — | new | [elementary-proof](../methods/elementary-proof/README.md) |
| [E29.1](E29.1/) | proved | Graham's {x, y, x+y, xy} colouring threshold starting at 3 is 3150 | [witness](E29.1/E29_1.lean) | new | [sat-threshold](../methods/sat-threshold/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [F6.2](F6.2/) | proved | Q(1,6,7) = ∞ and the other four-residue subpatterns of (1,6,7,10) | [full proof](F6.2/F6_2_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md) |
| [F19.1](F19.1/) | proved | every n ≥ 23 has two 3-part partitions with equal product | [full proof](F19.1/F19_1_mathlib.lean) | known | [parametric-family](../methods/parametric-family/README.md) |

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A3.11](A3.11/) | proved | more primes (16^p + 1)/17 beyond p = 317 | — | — | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [B2.3](B2.3/) | disproved | Kravitz's "no odd-square abundance" conjecture is false (already in the book) | [witness](B2.3/B2_3.lean) | — | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [B31.5](B31.5/) | disproved | the gcd of two binomial coefficients can have all prime factors ≤ r (already in the book) | [full proof](B31.5/B31_5.lean) | — | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [B36.7](B36.7/) | proved | infinitely many noncototients (already in the book) | — | — | [known-theorem](../methods/known-theorem/README.md) |
| [E10.3](E10.3/) | proved | Moser's base-3 collinearity question follows from density Hales–Jewett | needs Mathlib | — | [known-theorem](../methods/known-theorem/README.md) |
| [E25.1](E25.1/) | proved | the 20th term of Levine's sequence has been computed | — | — | [complete-table-scan](../methods/complete-table-scan/README.md) |
| [F10.2](F10.2/) | proved | a solution of 2^n ≡ 4 (mod n) with n ≡ 9 (mod 10) | [witness](F10.2/F10_2.lean) | known | [finite-witness-counterexample](../methods/finite-witness-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [F23.2](F23.2/) | trivial or misstated | n! = 2^a + 2^b only for n = 2, 3, 4 | [full proof](F23.2/F23_2_mathlib.lean) | — | [modular-obstruction](../methods/modular-obstruction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [F31.2](F31.2/) | proved | Coppersmith's 247 — no m with m and 247m both zero-free in balanced ternary | [full proof](F31.2/F31_2.lean) | — | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |

## Weaker results on open problems (the problem stays open)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [B4.5](B4.5/) | partial | unitary amicable pairs (infinitude, coprime pairs, an odd non-squarefree pair) | [full proof](B4.5/B4_5_mathlib.lean) | known | [complete-table-scan](../methods/complete-table-scan/README.md), [finite-witness-counterexample](../methods/finite-witness-counterexample/README.md) |
| [D16.1](D16.1/) | partial | least common product of m triples with one sum and one product, m = 2..11 | [witness](D16.1/D16_1.lean) | partly-known | [complete-table-scan](../methods/complete-table-scan/README.md), [lean-certificate](../methods/lean-certificate/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

### [A3.9](A3.9/): the smallest prime with digit sum k does not always end in 99

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section A3 (p. 16). De Koninck's questions, paraphrased: let p(k) be the
smallest prime whose decimal digits sum to k. Is p(k) ≡ 9 (mod 10) for k > 25, ≡ 99
(mod 100) for k > 38, and ≡ 999 (mod 1000) for k > 59?

**Result.** The second and third parts are false. p(86) = 6999999989, which is ≡ 89
(mod 100) and ≡ 989 (mod 1000). Further failures below k = 180: p(104) = 699999999989 and
p(137) = 3999999999999989. The mod-10 part holds for every 25 < k < 180 (k not a multiple of
3); it is not settled beyond that.

**Argument.** A number with digit sum 86 has at least 10 digits (9·9 = 81 < 86). A 10-digit
number with digit sum 86 is 9999999999 lowered by a total of 4 spread over its digits. In
increasing order these are 5999999999 (all 4 on the leading digit), then the numbers with
leading digit 6 and one further unit taken from one of the nine lower digits: 6899999999,
6989999999, …, 6999999899, 6999999989, 6999999998. The eight numbers before 6999999989 are
composite (factors 7, 6089, 827, 19, 61, 31, 7, 3011) and 6999999989 is prime
(trial division up to its square root, 83666).

Lean: [full proof](A3.9/A3_9_mathlib.lean).

### [A19.2](A19.2/): infinitely many n with every n − 2^k squarefree

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section A19
(values of n making n − 2^k prime). Alongside the prime question, Guy records Erdős's conjecture
that there are infinitely many n for which n − 2^k is squarefree for every k with 2^k < n.
OEIS [A091155](https://oeis.org/A091155) lists these n and says "Erdős conjectures that this
sequence is infinite". Original reference: P. Erdős, On integers of the form 2^k + p and some
related problems, *Summa Brasil. Math.* 2 (1950), 113–123.

**Reading.** k runs over all k ≥ 0 with 2^k < n (k = 0 included, so n − 1 must be squarefree).
n = 1 satisfies the condition vacuously; OEIS starts at 2. Neither affects infinitude.

**Result.** Proved: the set {n : n − 2^k is squarefree for every k ≥ 0 with 2^k < n} is
infinite. Quantitatively, for every s ≥ 20 there is such an n with s < n ≤ 2^(9702 s).

**Argument.** Fix s ≥ 20 and put y = 2310 s, L = 4851 s, K = 2L, x = 2^K. Let R be the product
of the odd primes ≤ y and M = 4R. Choose c < M with c ≡ 3 (mod 4) and R ∣ c (c = 3R if
R ≡ 1 mod 4, else c = R). The candidates are n_j = c + Mj for 0 ≤ j < J = ⌊x/M⌋ − 1; all are
≤ x, so for a candidate n the relevant k satisfy k < K.

1. *p = 2.* n ≡ 3 (mod 4), so n − 1 ≡ 2, n − 2 ≡ 1 and n − 2^k ≡ 3 (mod 4) for k ≥ 2. Hence
   4 ∤ n − 2^k.
2. *Odd p ≤ y.* p ∣ R ∣ n and p ∤ 2^k, so p ∤ n − 2^k.
3. *p > y.* If p² ∣ n − 2^k then p² < x, so p ≤ 2^L. For fixed (k, p) the candidates with
   p² ∣ n − 2^k are congruent to each other mod M (all ≡ c) and mod p² (all ≡ 2^k), and
   gcd(M, p²) = 1, so they are congruent mod Mp². Numbers ≤ x in one class mod Mp² number at
   most x/(Mp²) + 1.
4. *Prime sum.* A prime p > y ≥ 11 is coprime to 2310. Split m > 2310 s with gcd(m, 2310) = 1
   into blocks [2310 j, 2310 j + 2310), j ≥ s; each block holds φ(2310) = 480 such m, each with
   1/m² ≤ 1/(2310 j)². With 1/j² ≤ 1/(j−1) − 1/j (telescoping),
   Σ_{p prime, p > y} 1/p² ≤ (480/2310²) Σ_{j ≥ s} 1/j² ≤ 480/(2310² (s − 1)) =: σ.
   Then Kσ = 9702 s · 480 / (2310² (s − 1)) ≤ 23/25 for s ≥ 20 (it equals 0.9187 at s = 20 and
   decreases to 0.8727).
5. *Count.* Suppose no candidate is good. Each candidate lies in some set of step 3, so with
   a = x/M,
   a − 2 ≤ J ≤ Σ_{k<K} Σ_{y<p≤2^L} (x/(Mp²) + 1) ≤ K(aσ + 2^L) ≤ (23/25) a + K 2^L.
   So 2a ≤ 25 (K 2^L + 2). But R ≤ primorial(y) ≤ 4^y gives M ≤ 2^(2y+2) and
   a ≥ 2^(K − 2y − 2) = 2^(5082 s − 2) = 2^L · 2^(231 s − 2), while
   25 (K 2^L + 2) ≤ 242600 s · 2^L < 2^18 · 2^s · 2^L ≤ 2 · 2^L · 2^(231 s − 2). Contradiction.
6. So some candidate n is good. By Bertrand there is a prime q with 1155 s < q ≤ 2310 s = y;
   q is odd, so q ∣ R and n ≥ c ≥ R ≥ q > s. As s is arbitrary, there are infinitely many good n.

The only arithmetic input beyond counting is the primorial bound n# ≤ 4^n and Bertrand's
postulate. The block bound replaces a prime-counting estimate: the union bound needs
K Σ_{p>y} 1/p² < 1 while the modulus M must stay below about √x, and the crude bound
Σ_{m>y} 1/m² ≤ 1/y does not fit both with M ≤ 4^y; restricting m to residues coprime to 2310
(density 480/2310 ≈ 0.208) does, with K/y = 4.2 in the window (4, 4.81).

Lean: [full proof](A19.2/A19_2_mathlib.lean).

### [B2.1](B2.1/): every n ≥ 2 is a sum of two deficient numbers

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B2.
Guy asks (from *Abacus*) whether every integer n > 3 is the sum of two deficient numbers, that
is, numbers m with σ(m) < 2m. OEIS [A337932](https://oeis.org/A337932) counts the representations.

**Reading.** 1 is deficient (σ(1) = 1), so the statement holds for every n ≥ 2 and is proved in
that form. The two summands are positive integers; they may be equal.

**Result.** Proved: for every n ≥ 2 there are a, b ≥ 1 with a + b = n, σ(a) < 2a and σ(b) < 2b.

**Argument.** For t ≥ 1 write rs(t) = Σ_{d ∣ t, d > 1} 1/d. Since σ(t) = Σ_{d∣t} t/d,
σ(t) = t(1 + rs(t)), so t is deficient iff rs(t) < 1 (Markov-type counting below uses only this
identity). For a family t_0, …, t_{K−1}, swapping the sums gives
Σ_k rs(t_k) = Σ_{d>1} (1/d) · #{k : d ∣ t_k}.

*Even n = 2K.* Take the K pairs (2k+1, n−2k−1), k < K. If no pair has two deficient members,
each pair has rs ≥ 1 on one side, so K ≤ Σ_k rs(2k+1) + Σ_k rs(n−2k−1) = 2 Σ_k rs(2k+1)
(the second family is the first in reverse order). A divisor d of an odd number is odd, and the
odd numbers 2k+1 ≤ 2K divisible by d number at most 2K/d. Hence
Σ_k rs(2k+1) ≤ 2K Σ_{odd d ≥ 3} 1/d² ≤ 2K (1/9 + 1/8) = 2K · 17/72, using
1/d² ≤ 1/((d−1)(d+1)) = ½(1/(d−1) − 1/(d+1)), which telescopes over odd d ≥ 5 to 1/8.
So K ≤ (34/36) K, impossible for K ≥ 1. No threshold is needed.

*Odd n ≥ 300.* Choose r ∈ {1, 5} with 3 ∤ n − 2r (r = 5 if n ≡ 2 mod 3, else r = 1); let
c = n − 2r and K = ⌊c/12⌋ ≥ 24. For k < K let m_k = 6k + r and b_k = c − 12k, so
2m_k + b_k = n, and m_k, b_k are both coprime to 6. Since m odd gives σ(2m) = 3σ(m), the number
2m_k is deficient iff rs(m_k) < 1/3. A bad pair therefore gives 1 ≤ 3 rs(m_k) + rs(b_k), and
K ≤ 3 Σ_k rs(m_k) + Σ_k rs(b_k).
Every divisor d > 1 of m_k or b_k is coprime to 6, so d ≥ 5. If d divides m_k and m_{k'}, then
d ∣ 6(k − k'), so k ≡ k' (mod d); likewise d ∣ b_k, b_{k'} gives d ∣ 12(k − k'). So d hits at
most K/d + 1 indices, and each family sum is at most
K Σ_{odd d ≥ 5} 1/d² + Σ_{5 ≤ d ≤ n, (d,6)=1} 1/d ≤ K/8 + 11/8 + (n+1)/200,
where the harmonic part is bounded by its exact value below 200 (1.3743… ≤ 11/8) plus 1/200 for
each d ≥ 200. With n + 1 ≤ 12K + 23 this gives K ≤ K/2 + 11/2 + (12K + 23)/50, i.e. K ≤ 22,
a contradiction.

*2 ≤ n < 300.* Direct check (in Lean by kernel evaluation of σ).

Lean: [full proof](B2.1/B2_1_mathlib.lean).

### [B2.7](B2.7/): a harmonic number with two harmonic seeds

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B2 (p. 76). n is harmonic if H(n) = n·d(n)/σ(n) is an integer.
Cohen and Sorli call a harmonic number a seed if it has no smaller proper unitary divisor that
is harmonic (other than 1). Goto and Shibata ask, among other questions, whether every
harmonic number has a unique harmonic seed.

**Reading.** "Seed of n" = a harmonic seed that is a unitary divisor of n (a product of some of
the prime powers exactly dividing n). 1 is excluded.

**Result.** No. n = 2⁴·3·5²·7²·19·31²·83·331 = 29495815011600 (H = 525) has two seeds:
m₁ = n/5² = 1179832600464 (H = 217) and m₂ = n/3 = 9831938337200 (H = 350).

**Argument.** Of the 2⁸ unitary divisors of n, exactly three are harmonic and > 1: m₁, m₂, n.
A unitary divisor of m₁ is a unitary divisor of n, and m₂ is not a divisor of m₁; so m₁ has no
smaller harmonic unitary divisor > 1. The same holds for m₂. Hence both are seeds of n.
The scan also found no powerful and no deficient harmonic number > 1 below 10^14 (from the
OEIS A001599 list); that side remark was not rechecked.

Lean: [full proof](B2.7/B2_7_mathlib.lean).

### [B2.8](B2.8/): H(n) = 3p does not force a harmonic number to be arithmetic

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B2 (p. 76). Goto and Shibata note that every harmonic number n with
H(n) = 3p < 300 (p prime) is arithmetic (d(n) | σ(n)), and ask whether this holds for all
primes p.

**Result.** No. n = 2⁸·7·19²·37·73·113·127 = 25075635936512 has H(n) = 339 = 3·113 and
σ(n) ≡ 288 (mod d(n)). A second example: n = 2⁸·5²·7·19·31·37·73·179 = 12757657068800,
H(n) = 537 = 3·179, σ(n) ≡ 576 (mod d(n)).

**Argument.** Direct computation from the factorizations. (Equivalently, by Goto–Shibata,
a harmonic n is arithmetic iff H(n) | n; here 3 ∤ n, so 3p ∤ n.)

Lean: [full proof](B2.8/B2_8_mathlib.lean).

### [B10.3](B10.3/): Meeussen's numbers are not values of W(n) = n − d(n) − φ(n) + 1

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B10. Meeussen calls m < n unrelated to n if m neither divides n nor
is coprime to it; W(n) = n − d(n) − φ(n) + 1 counts them. He lists odd numbers (13, 67, 93,
…, 997, "…"; the first line is garbled in our copy) and asks whether any of them is a value
of W.

**Result.** None of them is a value of W. The odd non-values of W below 1000 are exactly 86
numbers: 13, 67, 93, 123, 133, 141, 173, 187, 193, 205, 217, 229, 245, 253, 257, 283, …, 973,
997. Every legible entry of the book's list is among them (the book's "498" is an OCR misread
of 493), and from 283 on the two lists agree term by term.

**Argument.** W(1) = W(2) = 0. For n ≥ 3, φ(n) is even, so W(n) is odd iff n − d(n) is even,
iff n is an odd square or an even non-square (d(n) is odd exactly for squares).
- n even: φ(n) ≤ n/2 and d(n) ≤ 2√n, so W(n) ≥ n/2 − 2√n + 1, which is ≥ 1000 once n > 2200.
- n = k² with k odd and prime: W = k² − 3 − k(k − 1) + 1 = k − 2, so W < 1000 needs k ≤ 1001.
- n = k² with k odd and composite: the least prime factor p of k is ≤ √k, so
  φ(n) ≤ n(1 − 1/p) and W(n) ≥ n/p − d(n) + 1 ≥ k^1.5 − 2k + 1 ≥ 1000 once k ≥ 120.

So W(n) < 1000 with W(n) odd forces n ≤ 1001² = 1002001, and a sieve of d and φ up to that
bound decides every odd m < 1000. (The scan's note gave the bound with the inequality
"d(k²) ≤ k", which alone gives only W ≥ 1; the bound itself is right, by the argument above.)

Lean: [full proof](B10.3/B10_3_mathlib.lean).

### [B16.6](B16.6/): 46 and 430 are the two smallest composite exceptions to the Ankeny–Artin–Chowla property

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B16. The Ankeny–Artin–Chowla conjecture says that for a prime
p ≡ 1 (mod 4), p does not divide u, where (t, u) is the least positive solution of
t² − p u² = 1. Guy notes the statement fails for non-prime d and that Myerson believes
46 and 430 are the two smallest counterexamples.

**Reading.** d ranges over non-square, non-prime integers > 1 and (t, u) is the least
positive solution of the Pell equation t² − d u² = 1, as in the book's wording.

**Result.** True. Among non-square non-prime d ≤ 430, d | u only for d = 46
((t, u) = (24335, 3588), u = 78·46) and d = 430 ((t, u) = (2862251, 138030), u = 321·430).

**Argument.** The least solution is the convergent of the continued fraction of √d at the end
of the first period (second period when the period length is odd). Computing it for every
non-square non-prime d ≤ 430 and testing d | u gives the two values.

Lean: [full proof](B16.6/B16_6_mathlib.lean).

### [B16.7](B16.7/): every gap occurs between consecutive squarefree numbers

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B16. With f₁ < f₂ < … the squarefree numbers, Panaitopol asks whether
for each positive integer k there is an n with f_(n+1) − f_n = k.

**Result.** Yes, for every k ≥ 1 (and for each k a positive proportion of integers m start
such a gap). The argument is elementary and very likely known.

**Argument.** Fix k ≥ 2 (k = 1: 1, 2). Choose distinct primes p₁, …, p_(k−1) and, by the
Chinese remainder theorem, a class c mod Q = ∏ p_i² with c + i ≡ 0 (mod p_i²) for 1 ≤ i < k.
For m ≡ c (mod Q) the numbers m + 1, …, m + k − 1 are not squarefree. It remains to find such m
with m and m + k squarefree. Write m = c + Qj. For p = p_i we have m ≡ −i and m + k ≡ k − i
(mod p_i²), both nonzero because 0 < i, k − i < k ≤ p_i², so p_i² divides neither. For any other
prime p, the conditions p² | m and p² | m + k each exclude one class of j mod p² (Q is invertible
mod p²). By the standard squarefree sieve the set of j avoiding all excluded classes has density
∏_(p ∉ {p_i}) (1 − 2/p²) > 0 (the tail p > z excludes O(J/z + √J) of j ≤ J). So such m exist,
and m, m + k are consecutive squarefree numbers.

Lean: [full proof](B16.7/B16_7_mathlib.lean).

### [B36.6](B36.6/): convergence of Σφ(n)/n^x and Σ(−1)^(n+1)φ(n)/n^x

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B36. Ecker asks for which x each of the two series
Σ φ(n)/n^x and Σ (−1)^(n+1) φ(n)/n^x converges.

**Reading.** x real (the question is a convergence exercise; for complex x the abscissa
argument below gives the same half-plane Re x > 2 for absolute convergence).

**Result.** Both converge exactly for x > 2. The problem is a standard exercise, not open.

**Argument.** - First series: terms are positive and Σ_(n≤N) φ(n) = (3/π²)N² + O(N log N), so by partial
  summation the series converges iff x > 2 (its sum is ζ(x − 1)/ζ(x)).
- Alternating series: for x > 2 it converges absolutely. For x ≤ 1 the terms do not tend to
  0 (φ(p)/p^x = (p − 1)/p^x along primes). For 1 < x ≤ 2: Σ_(n≤N, n odd) φ(n)/n = (4/π²)N + O(log N)
  and Σ_(n≤N) φ(n)/n = (6/π²)N + O(log N) (local factors ∏_(p>2)(1 − 1/p²) = 8/π²), so by partial
  summation Σ_(n odd ≤N) φ(n) = (2/π²)N² + O(N log N) and Σ_(n even ≤N) φ(n) = (1/π²)N² + O(N log N).
  Hence A(N) = Σ_(n≤N) (−1)^(n+1) φ(n) = N²/π² + O(N log N). Abel summation gives
  Σ_(n≤N) (−1)^(n+1)φ(n) n^(−x) = A(N)N^(−x) + x∫_1^N A(t) t^(−x−1) dt, which tends to +∞ for
  x < 2 (like N^(2−x)) and for x = 2 (like (2/π²) log N). So the series diverges for x ≤ 2.

Lean: [full proof](B36.6/B36_6_mathlib.lean).

### [B40.2](B40.2/): totatives of large n need not contain a Pythagorean triple

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B40. In a 1995 letter Recamán asks whether the set of totatives of
every sufficiently large n (the integers below n and coprime to n) contains a Pythagorean
triple.

**Result.** No, as stated: no n divisible by 2, 3 or 5 has a Pythagorean triple among its
totatives, and there are infinitely many such n. (For n coprime to 30 the question remains;
the scan's note sketches a sieve for that case, not checked here.)

**Argument.** If a² + b² = c², then 2 | ab (two odd squares sum to 2 mod 4, not a square),
3 | ab (two squares prime to 3 sum to 2 mod 3) and 5 | abc (squares prime to 5 are ±1 mod 5;
±1 ± 1 ∈ {0, ±2} mod 5 is never ±1). If p ∈ {2, 3, 5} divides n, every totative of n is prime
to p, so a, b, c cannot all be totatives.

Lean: [full proof](B40.2/B40_2.lean).

### [B40.3](B40.3/): totatives of large n contain k-term arithmetic progressions

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B40. Recamán asks whether, for each k, the totatives of every
sufficiently large n contain an arithmetic progression of length k.

**Result.** Yes, for every fixed k (elementary; very likely known).

**Argument.** Let D be the product of the primes ≤ k dividing n (D ≤ k!). Consider x_j(t) =
1 + jDt for 0 ≤ j < k and 1 ≤ t ≤ T = ⌊(n − 2)/((k − 1)D)⌋, so all terms lie in [1, n − 1].
For a prime p ≤ k dividing n, x_j ≡ 1 (mod p). For a prime p > k dividing n, D is invertible
mod p and x_j ≡ 0 (mod p) for some 1 ≤ j < k excludes at most k − 1 classes of t mod p.
Inclusion–exclusion over the set S of primes p > k dividing n gives at least
T·∏_(p∈S)(1 − (k − 1)/p) − k^|S| admissible t. Each factor is ≥ 2/(k + 1), and |S| ≤ ω(n) =
O(log n / log log n), so the main term is n^(1−o(1)) while k^|S| = n^(o(1)). For n large
(depending on k) some t is admissible, and x_0(t), …, x_(k−1)(t) is a k-term progression of
totatives.

Lean: [full proof](B40.3/B40_3_mathlib.lean).

### [B41.5](B41.5/): Finucane's lists for the iteration n → φ(n) + 1 are complete

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B41. Finucane iterates n → φ(n) + 1 (primes are fixed points) and
asks whether 5, 8, 10, 12 are the only numbers whose sequence ends at 5, and 7, 9, 14, 15, 16,
18, 20, 24, 30 the only ones ending at 7.

**Result.** Yes, both lists are complete.

**Argument.** The set of n reaching a prime q is closed under taking preimages, so it is
obtained from q by repeatedly solving φ(n) = m − 1. φ(n) is even for n ≥ 3, and the inverse
totient sets needed are φ⁻¹(4) = {5, 8, 10, 12}, φ⁻¹(6) = {7, 9, 14, 18},
φ⁻¹(8) = {15, 16, 20, 24, 30}, while 7, 9, 11, 13, 15, 17, 19, 23, 29 (odd) and 14 are not
totients. Preimages of 5: {5, 8, 10, 12}; of 8, 10, 12: none (7, 9, 11 are not totients).
Preimages of 7: {7, 9, 14, 18}; of 9: {15, 16, 20, 24, 30}; of 14, 18, 15, 16, 20, 24, 30:
none (13, 17, 14, 15, 19, 23, 29 are not totients). Inverse-totient sets are finite and
computable from φ(n) ≥ √(n/2).

Lean: [full proof](B41.5/B41_5_mathlib.lean).

### [D2.2](D2.2/): x^n + y^n = n!·z^n has a solution with n = 3

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section D2. Erdős asks for a proof that x^n + y^n = n!·z^n has no integer
solutions with n > 2 (nontrivial ones, xyz ≠ 0, understood).

**Result.** False for n = 3: 17³ + 37³ = 4913 + 50653 = 55566 = 6·21³. The case n = 4 has
no nontrivial solution (fourth powers are 0 or 1 mod 16 and 24z⁴ ≡ 0 or 8 mod 16, so x, y, z
are all even and descent applies). The cases n ≥ 5 are not addressed.

**Argument.** Direct computation.

Lean: [full proof](D2.2/D2_2.lean).

### [E4.3](E4.3/): Erdős's last question on primitive sets — the x²/6 guess is too small

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section E4 (p. 314). From an email Erdős sent a month before he died: for a
primitive set A ⊆ [1, x] (no element divides another), with f(A; n) the number of a_i < n, how
large can Σ_(n≤x) f(A; n) be? Is the maximum x²/6 + O(x), attained perhaps by the integers in
(x/3, 2x/3]?

**Reading.** The email is partly garbled in our copy. We read the sum as Σ_(n≤x) f(A; n) =
Σ_(a∈A) (x − a) (each a is counted for n = a + 1, …, x). This reading is supported by the
book's own numbers: the set (x/3, 2x/3] gives (x/3)(x/2) = x²/6. Counting a_i ≤ n instead
changes the sum by |A| ≤ x, inside the O(x).

**Result.** Under this reading the answer is no: the maximum is at least (13/64)x² − O(x)
≈ 0.2031x² > x²/6.

**Argument.** A = (x/4, x/2] ∪ {odd a ∈ (x/2, 3x/4]} is primitive: two elements of (x/4, x/2]
have ratio < 2; an odd a ∈ (x/2, 3x/4] and b ∈ (x/4, x/2] have 1 < a/b < 3, so b | a would
force a = 2b, which is even; two odd elements of (x/2, 3x/4] have ratio < 2. Its sum is
(x/4)(5x/8) + (x/8)(3x/8) + O(x) = (10/64 + 3/64)x² + O(x).

Lean: —.

### [E29.1](E29.1/): Graham's {x, y, x+y, xy} colouring threshold starting at 3 is 3150

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section E29.
Graham showed that every 2-colouring of [1, 252] contains x, y, x + y, xy of one colour (and 252 is
least), and asked about the analogous thresholds when the interval starts later.

**Reading.** x < y, both in the interval, and x, y, x + y, xy all in the interval and of one colour.
This convention reproduces Graham's 252 for the interval starting at 1 (x = 1 gives the triple
{1, y, y + 1}) and gives 990 starting at 2. Allowing x = y instead gives 39 and 450. From 3 on the
four numbers are automatically distinct, so the two readings that require distinctness agree.

**Result.** The least N such that every 2-colouring of [3, N] has x < y with x, y, x + y, xy
monochromatic is N = 3150.

**Argument.** Lower bound: an explicit colouring of [3, 3149] with no monochromatic quadruple.
Upper bound: the CNF with one variable per n in [3, 3150] and, for every x < y with xy ≤ 3150, the
two clauses "not all false" and "not all true" on {x, y, x + y, xy} is unsatisfiable.

Lean: [witness](E29.1/E29_1.lean).

### [F6.2](F6.2/): Q(1,6,7) = ∞ and the other four-residue subpatterns of (1,6,7,10)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section F6. Q(a,b,c) is the least R such that, for all sufficiently large
primes p, some r ≤ R has r, r + a, r + b, r + c all quadratic residues mod p (∞ if there is no
such R). Guy notes that although Q(1,6), Q(1,7), Q(5,6), Q(6,7) are finite, "it appears" that
Q(1,6,7) = ∞, and that all five four-element subpatterns of r + (0,1,6,7,10) seem to give ∞:
Q(1,6,7), Q(1,6,10), Q(1,7,10), Q(5,6,9), Q(6,7,10).

**Result.** All five are ∞.

**Argument.** Let f: ℕ → {±1} be completely multiplicative. By quadratic reciprocity and
Dirichlet's theorem, for every X there are infinitely many primes p with (ℓ/p) = f(ℓ) for all
primes ℓ ≤ X, hence (n/p) = f(n) for all n ≤ X. So Q(pattern) = ∞ as soon as some f has, for
every r ≥ 1, an element of r + pattern with f = −1.
- (0,1,6,7) and (0,1,7,10): f(n) = χ₋₄(odd part of n). For odd r, r and r + 6 (resp. r + 10)
  are odd and differ by 2 mod 4, so one is ≡ 3 (mod 4) and has f = −1; for even r use r + 1
  and r + 7.
- (0,1,6,10): Legendre symbol mod 11 (or 19); (0,5,6,9): mod 11 (or 17, 31); (0,6,7,10):
  mod 19; with any value at q itself. In each case every translate t + pattern mod q contains a
  nonzero non-residue class, so some element has f = −1. (This also works for (0,1,6,7) with
  q = 11, 17; (0,1,7,10) has no prime-modulus obstruction for q ≤ 31 and needs χ₋₄.)

Lean: [full proof](F6.2/F6_2_mathlib.lean).

### [F19.1](F19.1/): every n ≥ 23 has two 3-part partitions with equal product

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section F19. The first edition asked whether, writing n = a + b + c with
0 < a < b < c in every possible way, all products abc are distinct (Leech: no). Recamán
suggests the opposite: every sufficiently large n has two such partitions with equal products.

**Result.** True: every n ≥ 23 has two different partitions n = a + b + c, 0 < a < b < c,
with equal products. The exceptions are exactly n ≤ 18 and n = 22. (Allowing equal parts,
0 < a ≤ b ≤ c, the exceptions are n ≤ 12, 15 and 18.)

**Argument.** For t ≥ 37 and 0 ≤ s, w ≤ 18 put
A = (2t + 2s, 8t + 2s + 2w, 9t + 3w) and B = (3t + 3s, 4t + s + w, 12t + 4w).
Both sum to 19t + 4s + 5w and both have product 12(t + s)(4t + s + w)(3t + w)
(A = (2x, 2y, 3z), B = (3x, y, 4z) with x = t + s, y = 4t + s + w, z = 3t + w). For t ≥ 37 the
parts are strictly increasing in each triple and A ≠ B. Since 4s + 5w (0 ≤ s, w ≤ 18) takes
every residue mod 19 with 4s + 5w ≤ 162, every n ≥ 19·37 + 162 = 865 is covered. The range
23 ≤ n ≤ 864 is an explicit table.

Lean: [full proof](F19.1/F19_1_mathlib.lean).

### [A3.11](A3.11/): more primes (16^p + 1)/17 beyond p = 317

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section A3 (p. 16). McIntosh noted that the largest known prime of the form
(2^(4p) + 1)/17 had p = 317 and that it is composite for all primes 317 < p < 10000; Guy asks
whether there are any more.

**Result.** Yes, as probable primes. OEIS A057182 (numbers n with (16^n + 1)/17 prime) lists
n = 30197 (Robert G. Wilson v, 2005) and n = 1025393 (Paul Bourdelais, 2014, marked as a
probable prime). Both exponents are prime. This is a literature answer, not a resolution by
the scan.

**Argument.** None beyond the citation. No primality proof of either number was found; the
OEIS entry does not mention one, so the answer is at probable-prime level.

Lean: —.

### [B2.3](B2.3/): Kravitz's "no odd-square abundance" conjecture is false (already in the book)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B2 (p. 75). Kravitz conjectured that no n has abundance σ(n) − 2n
equal to an odd square. The same paragraph of the book reports Graeme Cohen's
counterexamples, including five of the form n = 2²·7²·p², the first being the smallest such n.

**Result.** False, and the book itself already says so. The scan did not add a resolution;
this entry records the check. Smallest example: n = 2²·7²·53² = 550564,
σ(n) − 2n = 41209 = 203².

**Argument.** For n = 2²·7²·p² with p ≠ 2, 7 prime, σ(n) = 7·57·(p² + p + 1), so
σ(n) − 2n = 7(p² + 57p + 57). This is an odd square for p = 53, 277, 541, 153941 (search to
10^6), matching Cohen's list.

Lean: [witness](B2.3/B2_3.lean).

### [B31.5](B31.5/): the gcd of two binomial coefficients can have all prime factors ≤ r (already in the book)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B31. Erdős and Szekeres ask whether the greatest prime factor of
gcd(C(n,r), C(n,s)), 0 < r < s ≤ n/2, always exceeds r. The book quotes the only
counterexample with r > 3 that they noticed, n = 28, r = 5, s = 14.

**Result.** No; the book already contains the counterexample, so this is a check, not a new
resolution. gcd(C(28,5), C(28,14)) = gcd(98280, 40116600) = 1080 = 2³·3³·5, greatest prime
factor 5 = r. With r ≤ 3 the counterexamples with n ≤ 60 are (n, r, s) = (10, 3, 5),
(16, 2, 6), (28, 3, 14).

**Argument.** Direct computation.

Lean: [full proof](B31.5/B31_5.lean).

### [B36.7](B36.7/): infinitely many noncototients (already in the book)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B36. A noncototient is an n for which x − φ(x) = n has no solution.
The book records that Browkin and Schinzel proved the Sierpiński–Erdős conjecture that there
are infinitely many noncototients (none of 2^k·509203, k ≥ 1, is of the form x − φ(x)); a
later paragraph of the same section restates the conjecture as open.

**Result.** True, by Browkin and Schinzel, as the book itself states. The scan's record is a
citation of the book, not a new resolution.

**Argument.** Not re-derived here.

Lean: —.

### [E10.3](E10.3/): Moser's base-3 collinearity question follows from density Hales–Jewett

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section E10. Moser maps n = Σ a_i 3^i to the lattice point (a₀, a₁, …) and
calls integers collinear if their images are. He conjectured that a sequence with no three
collinear has density zero, and asked whether f₃(n)/3^n → 0, where f₃(n) is the largest
number of points of {0,1,2}^n with no three on a line.

**Result.** Both hold. This follows from the density Hales–Jewett theorem for k = 3
(Furstenberg–Katznelson 1991; elementary proof by Polymath 2009/2012); it is a literature
consequence, not a new resolution.

**Argument.** DHJ(3): for every δ > 0, if n is large then every subset of {0,1,2}^n of size
≥ δ3^n contains a combinatorial line, which is a geometric line of three points. So
f₃(n) = o(3^n). For the integer version: if A has upper density δ > 0, pick N with
|A ∩ [0, N)| ≥ δN/2 and n with 3^(n−1) ≤ N < 3^n; then A ∩ [0, 3^n) has ≥ (δ/6)3^n elements,
whose images lie in {0,1,2}^n (higher digits are 0). For infinitely many such n DHJ(3)
gives three collinear images. So A has upper density 0.

Lean: needs Mathlib.

### [E25.1](E25.1/): the 20th term of Levine's sequence has been computed

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section E25. Lionel Levine's sequence (last entries of the rows of a
self-describing array) begins 1, 2, 2, 3, 4, 7, 14, 42, 213, 2837, …; Sloane knew fifteen
terms and wondered whether the 20th would ever be calculated.

**Result.** Yes. OEIS A011784 has a b-file "Table of n, a(n) for n = 1..20" by Johan Claes and
Roland Miyamoto (a(20) has about 356 digits; a(19) about 220). Related paper: "Golombic and
Levine sequences", arXiv:2602.10992 (2026). Literature answer, not a scan resolution.

**Argument.** None beyond the citation.

Lean: —.

### [F10.2](F10.2/): a solution of 2^n ≡ 4 (mod n) with n ≡ 9 (mod 10)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, F10 (residues of powers of two).
Paraphrase: Benkoski asked for a solution of 2^n ≡ 4 (mod n) whose last decimal digit is not 7; Zhang Ming-Zhi
(Sichuan Daxue Xuebao 27 (1990) 130-131) gave solutions with n ≡ 1 and 3 (mod 10) and asked whether there is one with
n ≡ 9 (mod 10).

**Result.** Yes. n = 1210344599 = 73 · 337 · 49199 has n ≡ 9 (mod 10) and 2^n ≡ 4 (mod n), and it is the smallest
such n. It is term number 26 of Max Alekseyev's complete list of odd solutions below 10^14 (OEIS
[A173572](https://oeis.org/A173572), b-file of 2012), which contains 35 solutions ≡ 9 (mod 10).

**Argument.** Direct computation: 2^1210344599 mod 1210344599 = 4. Minimality: exhaustive search over
n ≡ 9 (mod 10), n ≤ 1210344599.

Lean: [witness](F10.2/F10_2.lean).

### [F23.2](F23.2/): n! = 2^a + 2^b only for n = 2, 3, 4

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section F23. Erdős "observes that n! = 2^a + 2^b only when n = 1, 2, 3, 4
and 5" (the operator sign is as printed in our copy; it may be an OCR loss of ±).

**Result.** The statement is an observation, not an open problem, and as printed its list is
slightly off.
- "+" reading: the solutions are exactly n = 2, 3, 4 (2 = 1 + 1, 6 = 4 + 2, 24 = 16 + 8);
  1 < 2 ≤ 2^a + 2^b and 120 = 1111000₂ has four binary ones. So "only when n ≤ 5" is true,
  but n = 1 and n = 5 are not solutions.
- "−" reading, n! = 2^a − 2^b: the solutions are exactly n = 1, …, 5 (1 = 2 − 1, 2 = 4 − 2,
  6 = 8 − 2, 24 = 32 − 8, 120 = 128 − 8). This matches the printed list, so it is the likely
  intended statement (or "±").

**Argument.** - "+": 2^a mod 7 ∈ {1, 2, 4}, so 2^a + 2^b mod 7 ∈ {1, 2, 3, 4, 5, 6}, never 0, while 7 | n!
  for n ≥ 7. n ≤ 6 by inspection.
- "−": n! = 2^b(2^c − 1) with 2^b the 2-part of n!. For n ≥ 15, v₃(n!) ≥ ⌊n/3⌋, and 2^c − 1
  divisible by 3 forces c even, with v₃(2^c − 1) = 1 + v₃(c) (lifting the exponent for
  4^(c/2) − 1). So c ≥ 3^(⌊n/3⌋−1), while 2^c ≤ n! + 1 gives c ≤ n·log₂ n + 1;
  3^(⌊n/3⌋−1) > n log₂ n + 1 for n ≥ 15. For n ≤ 40, direct check (`misc_check.py`): the binary
  expansion of n! is a block of ones followed by zeros only for n ≤ 5.
  (The scan's note treated only "+" and missed that n = 1, 5 fail there.)

Lean: [full proof](F23.2/F23_2_mathlib.lean).

### [F31.2](F31.2/): Coppersmith's 247 — no m with m and 247m both zero-free in balanced ternary

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section F31. Selfridge and Lacampagne ask whether every k ≡ ±1 (mod 3) is
a quotient of two integers whose balanced-ternary digits are all ±1 (no 0). Coppersmith
answered negatively with k = 247 = 100011₃, claiming that no m has both m and 247m expressible
with digits ±1. The book reports the claim without proof.

**Result.** Coppersmith's claim is true (proved here in core Lean). 247 is the least positive
k ≢ 0 (mod 3) with this property; the others below 3000 are 277, 967, 977, 1211, 1219, 1895,
1937, 1951, 1961, 2183, 2191, 2911, 2921.

**Argument.** Write m = Σ e_i 3^i and 247m = Σ f_i 3^i with e_i, f_i ∈ {±1}, and read the
product from the least significant digit with carry c: c + 247e_i = f_i + 3c'. The carries
reachable from c = 0 after at least one digit form a set T of 28 even values in [−116, 116],
closed under the step. After the last digit of m the remaining carry must itself be the value
of a ±1 digit string (or 0); but T lies in a set D of nonzero integers closed under stripping
a ±1 digit (c → (c − f)/3), so no carry in T is such a value. And 247m cannot end before m
does, since |c| ≤ 124 < 247 ≤ |247·(nonzero)|.

Lean: [full proof](F31.2/F31_2.lean).

### [B4.5](B4.5/): unitary amicable pairs (infinitude, coprime pairs, an odd non-squarefree pair)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section B4 (paraphrased): a unitary amicable
pair (m, n) has σ*(m) = σ*(n) = m + n, where σ* sums the unitary divisors (d | N with gcd(d, N/d) = 1). Hagis asked
whether there are infinitely many (and infinitely many "twin" pairs with equal sums), conjectured that no coprime
pair exists, and asked for an odd pair that is not squarefree (such a pair would not be an ordinary amicable pair).

**Result.** Partial. The third question has an answer in published data: (m, n) = (581308455, 603131865) with
m = 3·5·7·13²·17·41·47 and n = 3·5·7·17·71·4759 is an odd unitary amicable pair and m is not squarefree. It is the
smallest such pair in J. M. Pedersen's table (OEIS A002952/A002953, all 7896 pairs with smaller member below
2·10^12); that table has 295 odd pairs, 56 of them not squarefree. The table has no coprime pair. Infinitude (and
the twin question) and the coprime conjecture remain open.

**Argument.** σ* is multiplicative with σ*(p^e) = 1 + p^e, so σ*(m) = 4·6·8·170·18·42·48 = 1184440320 = m + n and
σ*(n) = 4·6·8·18·72·4760 = 1184440320.

Lean: [full proof](B4.5/B4_5_mathlib.lean).

### [D16.1](D16.1/): least common product of m triples with one sum and one product, m = 2..11

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section D16.
Schinzel showed that arbitrarily many triples of positive integers can share both their sum and
their product. Guy suggests asking, for each multiplicity m, for the least common sum and the least
common product, and quotes (via Mauldon) sum 118 and product 25200 for m = 4.

**Reading.** A triple is (a, b, c) with 1 ≤ a ≤ b ≤ c. For each m, p(m) is the least P such that
some m distinct triples all have product P and one common sum. This is the "at least m" reading
(P may carry more than m triples with that sum). The least-sum question is OEIS
[A103277](https://oeis.org/A103277) (computed there for m ≤ 18, "exactly m" reading); this entry
does the product question, which is not in OEIS.

**Result.** For m = 2..11 the least common product p(m), with the common sum S of the extremal
triples:

| m | p(m) | S |
|---|---|---|
| 2 | 36 | 13 |
| 3 | 1200 | 39 |
| 4 | 25200 | 137 |
| 5 | 83160 | 185 |
| 6 | 776160 | 485 |
| 7 | 1965600 | 511 |
| 8 | 15724800 | 1022 |
| 9 | 34927200 | 1287 |
| 10 | 279417600 | 2574 |
| 11 | 1437836400 | 4279 |

No P ≤ 1.5·10^9 has 12 triples with one sum, so 1.5·10^9 < p(12) ≤ 11502691200 (the product
attached to the least sum 8558 in [A103278](https://oeis.org/A103278)). In this range the
"exactly m" reading gives the same values: the least P carrying a sum class of exactly m triples
is p(m) for every m ≤ 11. The extremal sum agrees with A103277 except at m = 4 and m = 6, where
the least-sum solutions (sums 118 and 400) have the larger products 37800 and 846720. So the
product sequence starts 36, 1200, 25200, 83160, 776160, and is not A103278.

**Argument.** Exhaustive search. For every P ≤ 1.5·10^9, factor P by a segmented sieve, list all
triples a ≤ b ≤ c with abc = P (a over divisors with a³ ≤ P, b over divisors of P/a with
a ≤ b ≤ √(P/a)), sort them by a + b + c and take the longest run. P is skipped only when the
upper bound (τ₃(P) + 3τ(P) + 2)/6 on its number of triples is below every multiplicity still
unrecorded, so no record can be missed.

Lean: [witness](D16.1/D16_1.lean).


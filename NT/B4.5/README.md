# Guy UPINT B4: unitary amicable pairs (infinitude, coprime pairs, an odd non-squarefree pair)

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

**Evidence.**
- Lean (Mathlib): [`B4_5_mathlib.lean`](B4_5_mathlib.lean), namespace `NT_B4_5`. Main theorem
  `odd_nonsquarefree_unitary_amicable`: with `usigma N = Σ_{d | N, gcd(d, N/d) = 1} d` (the definition),
  usigma m = usigma n = m + n, m ≠ n, both odd, m not squarefree. The two sums are evaluated by the kernel
  (`usigma_m`, `usigma_n`, via `Nat.divisors_mul` and `decide +kernel`). Also `m_fact`, `n_fact`, `primes`,
  `unitary_sums`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext,
  Classical.choice, Quot.sound.
- [`certificate/scan.py`](certificate/scan.py) with the b-files `b002952.txt`, `b002953.txt` (T. D. Noe, from
  Pedersen's site): recomputes σ* for all 7896 pairs (all are unitary amicable), lists the odd pairs and their
  factorizations, and finds no coprime pair.
- Outside Lean: completeness of Pedersen's table below 2·10^12 (used only for "smallest" and "no coprime pair
  below 2·10^12"); the open parts (infinitude, coprime pairs).

**Review level.** `lean-proof` for the example; the other two questions stay open.

**Prior art.** Checked 2026-11-06: the pair is in Pedersen's list of known unitary amicable pairs (via OEIS A002952,
A002953); McClung (Fibonacci Quart. 23, 1985) and Najar (IJMMS 18, 1995, all 185 pairs with smaller member below
10^8) extended Hagis's table. The scan's own search to 2·10^8 found only squarefree odd pairs, consistent with the
smallest odd non-squarefree pair being 5.8·10^8. Not in google-deepmind/formal-conjectures (clone of 2026-11-06).

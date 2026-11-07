# Guy UPINT B38: σ(y) = n! is solvable for 3 ≤ n ≤ 250 (partial)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section B38 (paraphrased): Erdős remarks
that φ(x) = n! is solvable and that, apart from n = 2, σ(y) = n! is probably solvable too.

**Result (partial; the general question stays open).** σ(y) = n! has a solution for every n with 3 ≤ n ≤ 250
(Lean), and for every n with 3 ≤ n ≤ 557 by an exact computation outside Lean. Previously known: 3 ≤ n ≤ 28
(Alekseyev, OEIS A055486, which counts all solutions).

**Argument.** σ is multiplicative, so y = ∏ q^a over distinct primes q gives σ(y) = ∏ (1 + q + … + q^a), and it
suffices to write n! as such a product. `certificate/search_small.py` (and `search.py` for larger n) fills the
exponents of the odd primes of n! from the largest prime down, choosing at random among atoms σ(q) = q + 1
(q ≤ B prime) and σ(q^a) (a ≥ 2, q < 2·10^4) that divide what remains and use a new q, with restarts; the remaining
power of 2 is then a subset sum of Mersenne exponents k ∈ {2, 3, 5, 7, 13, 17, 19} (σ(2^k − 1) = 2^k), using
Mersenne primes not already chosen. Example: n = 10, y = 3·7·19·5669, σ(y) = 4·8·20·5670 = 3628800 = 10!.

**Evidence.**
- Lean: [`B38_2_mathlib.lean`](B38_2_mathlib.lean), main theorem `B38_2_main : ∀ n, 3 ≤ n → n ≤ 250 →
  ∃ y, sigma 1 y = n !` (Mathlib `ArithmeticFunction.sigma`). The witness table (bases q ≤ 10^5 and Mersenne
  primes up to 2^19 − 1) is checked by the kernel in 31 chunks: distinct prime bases by trial division
  (`OpenProblemsLib.ArithFactor.factCheck`) and ∏ σ(q^a) = n!; `sigma_val` gives σ(y). Checked with
  `tools/leancheck-mathlib.sh`; axioms propext, Classical.choice, Quot.sound.
- Computation (`certificate/search.py 3 1000 4000000`): witnesses for 3 ≤ n ≤ 557 (`certificate/witnesses_3_557.txt`; the run stopped at its 50-minute limit), each verified in Python
  with exact integer arithmetic (∏ σ(q^a) = n!, bases distinct, primality by Miller–Rabin with the first twelve
  prime bases, deterministic below 3.3·10^24, all bases < 2^31).
- Outside Lean: the range 251 ≤ n ≤ 557 (Python check).

**Review level.** `lean-witness` for n ≤ 250; `agent` above.

**Prior art.** Checked 2026-11-07: OEIS A055486/A055488 (Alekseyev, J. Integer Seq. 19 (2016) 16.5.2: counts for
n ≤ 28); notes/NT-B38.2.md of the scan (2026-11-01: no proof for all n); web search; not in
google-deepmind/formal-conjectures (clone of 2026-11-06). The extension past 28 appears new; it is an easy
computation once one searches for a single solution instead of counting all of them.

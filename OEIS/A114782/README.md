# OEIS A114782: "a(n) = 0 iff prime(n) + 1 == 0 (mod 3)" is false

**Source.** [A114782](https://oeis.org/A114782): smallest prime of the form 10^k + prime(n) with k >= d, d the number
of digits of prime(n); 0 if no such prime exists. Comment in the entry: "Conjecture a(n) = 0 iff prime(n) + 1 == 0
(mod 3)." (OEIS text, checked 2026-11-07.)

**Result.** False in the direction "a(n) = 0 => prime(n) == 2 (mod 3)". For p = prime(4966) = 48247 (p == 1 mod 3)
every 10^k + p is composite, so a(4966) = 0. The other direction holds: p == 2 (mod 3) gives 3 | 10^k + p.

**Argument.** 10 has order 6, 2, 6, 3 modulo 7, 11, 13, 37. With p = 48247: 7 | 10^k + p for k == 4 (mod 6),
11 | for k odd, 13 | for k == 2 (mod 6), 37 | for k == 0 (mod 3). These classes cover all k mod 6, and
10^k + p > 37, so 10^k + p always has a proper factor.

**Evidence.** [`A114782_mathlib.lean`](A114782_mathlib.lean), main theorem `A114782_conjecture_false`:
∃ n, A114782 n = 0 ∧ (prime(n) + 1) % 3 ≠ 0, with `A114782` the OEIS definition (via `Nat.nth Nat.Prime`, offset 1).
Primality of 48247 by a Pratt certificate; covering by `decide +kernel` plus a periodicity lemma. Axioms: propext,
Classical.choice, Quot.sound. Outside Lean: nothing beyond reading the definition. `certificate/find_cover.py` finds
the covering sets; `certificate/covering_search.py` builds a different counterexample (p = 141870409207, cover
{7, 11, 37, 101, 9901}). The smallest counterexample is not determined: smaller p == 1 (mod 3) such as 2971 have no
known covering and no known prime 10^k + p (Prime Puzzles 556).

**Review level.** lean-proof.

**Prior art.** Partly known: Prime Puzzles & Problems, Puzzle 556 (W. Edwin Clark; proofs by Andersen, Resta, Clark),
https://www.primepuzzles.net/puzzles/puzz_556.htm, lists 48247, 56473, ... with p + 10^n always composite via
{7, 11, 13, 37}; it is not linked to A114782 there. google-deepmind/formal-conjectures (HEAD 2026-11-06) and
otoi-lab/oeis-lean-proofs: no entry. Checked 2026-11-07.

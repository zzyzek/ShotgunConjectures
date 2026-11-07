# Guy D11: Johnson's 48 semiprime unit fractions summing to 1 are not minimal

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section D11.
Erdős and Graham showed that unit fractions with squarefree denominators having exactly ω prime
factors represent 1. For ω = 2 at least 38 terms are needed, and Allan Johnson found 48 such
terms. Guy asks whether 48 is the smallest possible number.

**Result.** No. There are 47 distinct squarefree semiprimes whose reciprocals sum to 1:

6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 82, 85, 86, 87,
91, 93, 95, 106, 111, 123, 133, 145, 155, 159, 185, 203, 215, 253, 265, 287, 319, 493, 583, 731,
851, 1073.

**Argument.** Direct exact computation. The least common multiple is 693386350578511590.

**Evidence.**
- Lean (core): [`D11_4.lean`](D11_4.lean). `D11_4_main` states that the list has 47 distinct
  entries, each is p·q with p < q primes (`IsPrime` is the usual definition, obtained from a
  bounded trial-division check by `isPrimeSmall_sound`), and that the sum of reciprocals in `Rat`
  is 1 (`decide +kernel`). `D11_4_not_min` gives a set of fewer than 48 terms. Axioms propext,
  Classical.choice, Quot.sound. Outside Lean: none for the answer "no".
- `certificate/check_47.py` (second reader, `fractions` + `sympy`).
- Not checked: the true minimum. Watanabe states (Prime Puzzles 899, entry dated Oct 30, 2026) a
  computer-assisted proof that 46 terms are impossible, with exactly 23 sets of 47 terms; that
  search is not reproduced here.

**Review level.** `lean-witness`.

**Prior art.** Known. The 47-term set was posted by Tatsuru Watanabe on
[Prime Puzzles & Problems, Puzzle 899](https://primepuzzles.net/puzzles/puzz_899.htm) (the
page dates his first post "Set 8, 2010"; it lists 17 such sets). Searched: web,
google-deepmind/formal-conjectures (Erdős 306 concerns a different question), arXiv 2606.15159
(S. Li, existence for every natural number, no term counts). 2026-11-07.

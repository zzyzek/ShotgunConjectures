# OEIS A214305: Coman's residue conjecture for Poulet numbers fails

**Source.** OEIS [A214305](https://oeis.org/A214305) (Fermat pseudoprimes to base 2 with two
prime factors), conjecture 2 by Marius Coman (2012): "Any Poulet number p2 divisible by d can be
written as (p1 - d)*n + d, where n is a positive integer, if there exists a smaller Poulet number p1
with two prime factors divisible by d." (OEIS text, CC BY-SA 4.0.) Conjectures 1 and 3 assert
infinitely many such p2 for d the largest prime factor of p1.

**Reading.** d is not specified in conjecture 2. Two readings: d any prime of p1, or (as in
conjectures 1 and 3) d the largest prime factor of p1.

**Result.** Conjecture 2 is false under both readings.
- d any prime: p1 = 341 = 11·31, p2 = 561 = 3·11·17, d = 11: 561 - 11 = 550 is not a multiple of
  341 - 11 = 330.
- d largest: p1 = 23377 = 97·241, p2 = 34945 = 5·29·241, d = 241: 34704 is not a multiple of 23136.
  23377 is the only two-factor Poulet number below 34945 with largest factor 241, so this also
  defeats the reading "for some qualifying p1". Another: p1 = 5461 = 43·127, p2 = 55245 = 3·5·29·127.
Conjectures 1 and 3 ("infinitely many") are not addressed.

**Argument.** Direct computation (Fermat condition 2^(n-1) ≡ 1 mod n, factorisations, the failed
divisibilities).

**Evidence.**
- [`A214305.lean`](A214305.lean): all six numbers are Poulet numbers (`decide +kernel` on
  2^(n-1) mod n), factorisations, primality of the factors by trial division, and the three failed
  divisibilities. Outside Lean: the uniqueness of the qualifying p1 below 34945 (only needed for
  the "some p1" reading).
- `certificate/a214305_strict.py`: scan of the Feitsma–Galway table below 2·10^5 for p2 failing for
  every qualifying p1 (largest-factor reading): 34945, 55245, 87249, 129921, 150851, 158369, ...
- Lean (Mathlib): [`A214305_mathlib.lean`](A214305_mathlib.lean), `A214305_main`: the three counterexamples with `Nat.FermatPsp _ 2`, and every Poulet number below 34945 divisible by 241 is 23377 (so the "some qualifying p1" reading fails too). Nothing outside Lean.

**Review level.** `lean-proof` for conjecture 2 false (Mathlib file above); conjectures 1 and 3 not addressed.

**Prior art.** Known. [OEIS A214305](https://oeis.org/A214305) (fetched 2026-11-04) already contains E. Rodríguez's Sep 2026 comment with the counterexample p1 = 23377, p2 = 34945, d = 241 ([history](https://oeis.org/history?seq=A214305)). Our 'any prime d' reading counterexample (341, 561) is not there but is minor. Searched: entry, OEIS cross-reference search, edit history. (Prior-art review 2026-11-04.)

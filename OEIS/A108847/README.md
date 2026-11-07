# OEIS A108847 / A068689: 9 d…d 9 is composite for every inner digit d other than 1, 2, 8

**Source.** OEIS [A108847](https://oeis.org/A108847) (palindromic primes with all internal digits 8), old
comment by Cino Hilliard (2005): "Inner digits 1 and 2 are the only repeating digits for which s(x) is
prime for outer digits 9. I.e. 9444..4449, 9555..5559, 9777..7779 are composite." On 2023-01-28 Michel
Marcus moved the comment to [A068689](https://oeis.org/A068689) (primes 9 d…d 9), where it now reads
"Inner digits 1, 2 and 8 are the only repeating digits for which the resulting numbers can be prime"
and is still labelled a conjecture (checked 2026-11-07). (OEIS text CC BY-SA 4.0.)

**Reading.** N(d, k) is the number with decimal digits 9, then k ≥ 0 copies of d, then 9.

**Result.**
- The A108847 wording is false: 9888889 (d = 8) is prime, and it is a term of A108847 itself
  (J. E. Schoenfield raised this in the 2023 edit discussion).
- The corrected A068689 statement is true: if N(d, k) is prime then d ∈ {1, 2, 8}; and 919, 929,
  9888889 are prime.

**Argument.** 9·N(d, k) = (810 + 10d)·10^k + (81 − 10d). Mod 3003 = 3·7·11·13 the value of N(d, k)
has period 6 in k, since 3003 divides 10^6 − 1 and 111111. For d ∈ {0, 3, 4, 5, 6, 7, 9} each of the six
residues is divisible by one of 3, 7, 11, 13 (d = 4: k ≡ 0..5 mod 6 → 13, 11, 3, 11, 7, 3 for k = 1..6;
d = 5: 7, 11, 3, 11, 13, 3; d = 7: 11 always, as 9N = 11(80·10^k + 1); d = 0, 3, 6, 9: 3). Since
N ≥ 99 > 13, N is composite.

**Evidence.**
- Lean (Mathlib): [`A108847_mathlib.lean`](A108847_mathlib.lean). `A108847_main` (N(d, k) prime, d ≤ 9
  ⇒ d ∈ {1, 2, 8}), `A108847_digits` (the decimal digits of `A108847_N d k` are exactly 9, d^k, 9),
  `A108847_witness` (919, 929, 9888889 prime), `A108847_comment_false`. Axioms propext,
  Classical.choice, Quot.sound. Outside Lean: none.
- `certificate/smallfactor_scan.gp`, `certificate/smallest_factor_table.gp`: smallest prime factors
  for k ≤ 120 (exploration only).

**Review level.** `lean-proof`.

**Prior art.** OEIS A108847 and A068689 entries and histories (2026-11-07); web search for the
9 d…d 9 families; google-deepmind/formal-conjectures (HEAD 2026-11-06) and otoi-lab/oeis-lean-proofs
have neither number. No proof of the composite part found; Branicky's 2023 searches are numerical.

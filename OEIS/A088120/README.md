# OEIS A088120: the common difference is 2 at n = 12

**Source.** [A088120](https://oeis.org/A088120) (smallest prime of the form a(a+d)···(a+(n−1)d) + d),
comment: "Conjectures: (1) Sequence is infinite. (2) The common difference arising = 1 except for n = 4 and 5
in which case it is 2." (OEIS text, CC BY-SA 4.0.)

**Result.** Conjecture (2) is false: a(12) = 1·3·5···23 + 2 = 316234143227, with d = 2 (the entry's own data
lists this value). The scan also found d ≠ 1 at n = 24 (d = 2) and n = 33, 39 (d = 3); not re-checked here.
Conjecture (1) is not addressed.

**Argument.** The values ≤ W = 316234143227 are k(k+1)···(k+11) + 1 for k = 1..4 (12!+1 = 13²·2834329,
13!+1 = 83·75024347, 14!/2+1 = 31·4289·327839, 15!/6+1 = 32009·6808889) and W itself; k = 5 (d = 1), a = 2
(d = 2) and any d ≥ 3 give larger values, as the product grows with a and d. W is prime.

**Evidence.**
- Lean (Mathlib): [`A088120_mathlib.lean`](A088120_mathlib.lean) proves the full result (`A088120_main`): 316234143227 is the least prime of the form a(a+d)...(a+11d) + d (Mathlib `IsLeast`; primality by a Pratt certificate, monotonicity by `Finset.prod_le_prod`), and every representation has d = 2. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`A088120.lean`](A088120.lean): the four factorizations and the bounds on the next candidates.
  Outside Lean: primality of W (sympy, deterministic below 2^64; PARI `isprime`) and monotonicity in a, d.
- `certificate/check.py` (enumeration with factorizations); `a088120.gp`, `a088120_verify.gp` (scan scripts, n ≤ 45).

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A088120_mathlib.lean`](A088120_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A088120.lean`](A088120.lean) checks the parts named under Evidence.
**Prior art.** New: no one has noted that conjecture (2) fails at n = 12, although a(12) is in the entry's own data. [A088120](https://oeis.org/A088120) is unchanged since 2013. Searched OEIS entry, references and history. Checked 2026-11-04.

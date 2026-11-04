# Guy F31: Coppersmith's 247 — no m with m and 247m both zero-free in balanced ternary

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

**Evidence.**
- Lean: [`F31_2.lean`](F31_2.lean), theorem `no_multiplier`: for every nonempty ±1 digit
  list es and every ±1 digit list fs, 247·ev(es) ≠ ev(fs) (core Lean; axioms propext,
  Classical.choice, Quot.sound from `decide` on list membership). Nothing outside Lean except
  the (standard) uniqueness of balanced-ternary representations used to phrase the statement.
- `certificate/f312_check.py` (second reader): the carry sets and the list of failing k < 3000;
  scan script `coppersmith247.py` copied. Minimality of 247 is from these scripts, not Lean.

**Review level.** `lean-proof`.
**Prior art.** Coppersmith's claim as reported by Guy; no published proof was looked for.
This record is not in the repository index (`problems.jsonl`), because the scan classed it as
answered in the source. 2026-11-01.

# Guy UPINT C18: Heden's modular queens, M(n) = n - 2 when 3 | n or 4 | n

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section C18 (paraphrased): on the n × n
board whose rows, columns and diagonals wrap around, Heden showed that the maximum number M(n) of non-attacking
queens is n, n - 1 for gcd(n,6) = 1, gcd(n,12) = 2, and lies in [n-4, n-2] or [n-5, n-2] when gcd(n,12) is 3 or 4,
respectively 6 or 12. Heden believed M(n) = n - 2 in the last two cases.

**Reading.** Two queens at (x, y), (x', y') in ZMod n × ZMod n attack iff x = x', y = y', x + y = x' + y' or
y - x = y' - x'. The question covers every n ≥ 3 with 3 | n or 4 | n.

**Result.** Known: M(n) = n - 2 whenever 3 | n or 4 | n. P. Monsky, solution to E3162, Amer. Math. Monthly 96 (1989)
258-259; a complete proof with explicit placements is in K. Williams, *Torus Queen Independence*,
arXiv:2404.18237 (2024), Theorem 6 (independence number n for n ≡ ±1 mod 6, n - 1 for n ≡ ±2 mod 12, n - 2
otherwise). Guy's 3rd edition (2004) still lists the question as open.

**Argument.** Lower bound: columns t = 0..n-1 minus two excluded columns, queen at (t, Y(t)) with Y piecewise linear
(Williams, five residue families n = 6m+3, 12m+4, 12m+6, 12m-4, 12m, plus n = 4, 6, 12 by hand). For t1 < t2 the
differences of y, x + y and y - x lie strictly between -7n and 7n, and none is a multiple of n.
Upper bound (Monsky; Williams' write-up): if n - 1 queens existed, the four coordinate maps each miss one value
a, b, c, d. Summing gives c = a + b - S1, d = S1 - a + b with S1 = n(n-1)/2. Summing squares (for even n, squares of
lifts in [0, n) taken mod 2n) with (x+y)² + (y-x)² = 2x² + 2y² forces n | Σ_{v<n} v² (odd n, or 3 | n) or the same
modulo 2n (4 | n), which fails because (n-1)(2n-1) is prime to 3 and odd.

**Evidence.**
- Lean (Mathlib): [`C18_4_mathlib.lean`](C18_4_mathlib.lean), namespace `NT_C18_4`. Main theorem
  `modular_queens_eq`: for every n ≥ 3 with 3 ∣ n ∨ 4 ∣ n there is S ⊆ ZMod n × ZMod n with |S| = n - 2,
  pairwise non-attacking (`queens_lower`), and every pairwise non-attacking S has |S| ≤ n - 2 (`queens_upper`,
  Monsky's argument; `miss` gives the missing value of an injective map, `sq_lift` the mod-2n squares).
  Each family is proved for all m (`F3_ok`, ..., `F12_ok`: per multiple k·n, |k| ≤ 6, `omega` on every pair of
  pieces); `family_to_finset` turns a family into the Finset statement. Check: `tools/leancheck-mathlib.sh`, exit 0,
  no warnings; axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/williams.py`](certificate/williams.py): the same placements checked for every n ≤ 600;
  [`certificate/gen_lean.py`](certificate/gen_lean.py) generates the family lemmas (parts `head.lean`,
  `fam_part.lean`, `bridge.lean`, `tail.lean`, `upper.lean` are concatenated into the Lean file).
- Outside Lean: none beyond reading M(n) as the maximum size of a pairwise non-attacking set.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: Monsky 1989 (cited as the full resolution in Williams, arXiv:2404.18237, and in
Burger-Cockayne-Mynhardt, Australas. J. Combin. 24 (2001)); not in google-deepmind/formal-conjectures (clone
2026-11-06, only GreensOpenProblems/97 mentions queens) or otoi-lab/oeis-lean-proofs.

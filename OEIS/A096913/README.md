# OEIS A096913: 0 and 3844 are the only squares (known; proved in Lean)

**Source.** OEIS [A096913](https://oeis.org/A096913) (numbers k such that (largest digit of
k)^(smallest digit of k) + k is a square), comment: "Conjecture: 0 and 3844 are the only squares
in this sequence." (OEIS text, CC BY-SA 4.0.) A later comment in the entry by Maon Wenders
(Jun 02 2012) explains why only finitely many squares can occur and reports an exhaustive PARI
search finding no others.

**Reading.** Digits in base 10; 0 has the single digit 0 and 0^0 = 1 (so 0 is a term, as in
the entry's data).

**Result.** True: if k = s² and k + a^b = t² with a, b the largest and smallest digits of k,
then k ∈ {0, 3844} (3844 = 62², 8³ + 3844 = 66²).

**Argument.** If a = 0 then k = 0. Otherwise d = a^b ≥ 1, so t = s + j with j ≥ 1 and
d = j(2s + j). Hence j² ≤ d, j divides d, d/j − j = 2s is even and s = (d/j − j)/2. For each of
the pairs (a, b) with a, b ≤ 9 and each j ≤ ⌊√(a^b)⌋ (67 000 values in all) the candidate s is
computed and the digits of s² are tested; only s = 0 and s = 62 pass.

**Evidence.**
- Lean (core): [`A096913.lean`](A096913.lean). `A096913_squares` (all s, t: the statement
  above), `A096913_3844` (both squares are terms). The finite check is split into kernel
  evaluations (`decide +kernel`) of at most 5000 values of j each. Axioms propext,
  Classical.choice, Quot.sound; zero warnings. Outside Lean: none.
- `certificate/solve.py`: the same enumeration in Python (207 candidates s, solutions 0, 3844).

**Review level.** `lean-proof`.

**Prior art.** Settled in the entry itself by Wenders's 2012 comment (search, no written
proof); the argument above is the divisor form of his "offset to the next square" bound.
google-deepmind/formal-conjectures (clone of 2026-11-06) and otoi-lab/oeis-lean-proofs have no
file for A096913. Checked 2026-11-07.

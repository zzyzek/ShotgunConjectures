# OEIS A158233: the terms are only 0, 3, 4, 6

**Source.** [A158233](https://oeis.org/A158233) (offset 1), Paul Curtz, Mar 14 2009, edited by R. J. Mathar:
"a(n) = A120070(n+1)*A120070(n+2) mod 9." Comment: "Conjecture: this contains only the numbers 0,3,4,6 (verified
for the first 5000 terms)." [A120070](https://oeis.org/A120070) (offset 2) is the triangle T(m,l) = m^2 - l^2,
1 <= l <= m-1, read by rows: 3, 8, 5, 15, 12, 7, ... (OEIS text, CC BY-SA 4.0, A158233 revision #6 of Feb 03 2019,
checked 2026-11-06.)

**Reading.** A120070(i) for i >= 2 is the i-th entry of the triangle read row by row, exactly as in the entry's
Maple program (A120070flat). With this reading the entry's data a(1..105) is reproduced.

**Result.** True: a(n) is 0, 3, 4 or 6 for every n >= 1, and all four values occur. Moreover a(n) = 4 exactly when
3 does not divide the product.

**Argument.** Two consecutive terms of A120070 are either in one row, T(m,l) and T(m,l+1) with l+1 <= m-1, or the
end of row m = l+1 and the start of row l+2, that is 2l+1 and (l+2)^2 - 1 = (l+1)(l+3).
- Across rows: (2l+1)(l+1)(l+3) is divisible by 3 (if l = 0 mod 3 then 3 | l+3, if l = 2 then 3 | l+1, if
  l = 1 then 3 | 2l+1). So the residue mod 9 is 0, 3 or 6.
- In a row: if 3 divides (m^2 - l^2)(m^2 - (l+1)^2), the residue is 0, 3 or 6. Otherwise m^2 differs mod 3 from
  both l^2 and (l+1)^2. Squares mod 3 are 0 or 1, so l^2 = (l+1)^2 mod 3, forcing l = 1 mod 3 and then m = 0 mod 3.
  Then the product is l^2 (l+1)^2 = (l(l+1))^2 mod 9, and l(l+1) = 2 mod 9 for l = 1, 4, 7 mod 9, so the residue is 4.

**Evidence.**
- Lean (Mathlib): [`A158233_mathlib.lean`](A158233_mathlib.lean). Definitions: `pos i` (cell of the i-th term,
  the Maple walk), `A120070 i = m^2 - l^2`, `A158233 n = (A120070 (n+1) * A120070 (n+2)) % 9`. Main theorem
  `OEIS158233.A158233_values : 1 ≤ n → A158233 n = 0 ∨ A158233 n = 3 ∨ A158233 n = 4 ∨ A158233 n = 6`; also
  `A158233_attained` (a(1..4) = 6, 4, 3, 0). Route: `pos_inv` (1 <= l < m), cast to `ZMod 9` (`cast_sq_sub`),
  and `key_row`, `key_cross` check all residues by `decide`. Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): computes 199989 terms from the definition, matches the entry's
  data, all terms in {0, 3, 4, 6}; checks the residue tables.
- Outside Lean: none. Not verified in Lean: agreement of `A158233` with the OEIS data terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry (revision #6, 2019) still states it as a conjecture; A120070's
history adds nothing on it. Not in google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/158233.lean`)
or otoi-lab/oeis-lean-proofs. A web search found only the entry. The argument is immediate.

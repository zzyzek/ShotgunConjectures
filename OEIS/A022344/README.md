# OEIS A022344: Fibonacci sequences in the Wythoff array and the product of characteristics

**Source.** [A022344](https://oeis.org/A022344) (Allan Wechsler's "J determinant"; a(n) = ⌊(n+1)τ⌋² − n⌊(n+1)τ⌋ − n²).
Comment of Kenneth J. Ramsey, Feb 11 2007: "Conjecture: Every pair of Fibonacci sequences, F1 and F2, appear in rows n
and m of Wythoff's Array, respectively and have respective characteristics a(n) and a(m). Also, there is a third
Fibonacci sequence F3, defined by F3(i) = F1(i) * F2(j+1) - F1(i+1)*F2(j) where j is held constant. The sequence F3
appears in row p of Wythoff's array and has the characteristic a(p) = a(n)*a(m)." The characteristic of a row is
|T(i)² − T(i−1)T(i+1)| (Ramsey, 2007 comment). (OEIS text, CC BY-SA 4.0, revision #45 of Nov 05 2025, checked
2026-11-06.)

**Reading.** "Fibonacci sequence": integer sequence with F(i+2) = F(i+1) + F(i), eventually positive (the rows of the
Wythoff array are positive); "appears in row n": agrees with row n from some index on, after a shift of index.
Rows are indexed so that row n has characteristic a(n) (A022344 has offset 0; the first Wythoff row 1, 2, 3, 5, ...
has characteristic 1 = a(0)).

**Result.** True up to sign, and known. (1) Every eventually positive Fibonacci sequence is, after finitely many
terms and a shift, a row of the Wythoff array (D. R. Morrison 1980); its characteristic is constant along the
sequence and equals that of the row. (2) F3 is a Fibonacci sequence with characteristic char(F1)·char(F2), since
D_{F3}(i) = D_{F1}(i)·D_{F2}(j) with D(i) = F(i+1)² − F(i)F(i+2) (the norm in Z[φ] is multiplicative). F3 is
eventually of constant sign but can be negative: F1 = F2 = Fibonacci numbers, j = 1 give F3(i) = −F(i−1). So the
row in the conjecture is that of |F3| (for F3 < 0, F3 itself is not a row). The product rule is Peter Munn's
A357097 (2022), stated there as A022344(A(x,y)) = A022344(x)·A022344(y).

**Argument.** (1) With x = F(i), y = F(i+1): D(i+1) = (x+y)² − y(x+2y) = x² + xy − y² = −D(i), so |D| is
constant. Since a positive Fibonacci tail is a row tail (Morrison), the characteristic is that row's, a(n).
(2) F3(i) is a fixed integer combination of F1(i), F1(i+1), so F3 satisfies the recurrence, and expanding gives
D_{F3}(i) = (y² − xy − x²)(v² − uv − u²) with u = F2(j), v = F2(j+1). F3 is not identically zero (D ≠ 0) and a
nonzero integer Fibonacci sequence is eventually of one sign, so |F3| eventually is a positive Fibonacci sequence,
hence a row tail p with a(p) = a(n)a(m).

**Evidence.**
- Lean (core): [`A022344.lean`](A022344.lean): `char_const` (characteristic independent of i), `F3_fib`, `D_F3`,
  `char_F3` (char F3 = char F1 · char F2), `F3_negative_example` (F3 for Fibonacci, j = 1, at i = 5 is −3). Check:
  `tools/leancheck.sh`, exit 0; axioms propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): rows 1..300 of the Wythoff array have characteristic
  A022344(n−1); in 127 random cases (rows ≤ 30, j ≤ 5) |F3| is found as a row with a(p) = a(n)a(m).
- Outside Lean: Morrison's theorem (every eventually positive Fibonacci sequence is a row tail), that row n has
  characteristic a(n) (formula of the entry), and the eventual constant sign of F3.

**Review level.** `lean-witness`.

**Prior art.** Checked 2026-11-06. D. R. Morrison, "A Stolarsky array of Wythoff pairs", in A Collection of
Manuscripts Related to the Fibonacci Sequence, Fibonacci Association, 1980, pp. 134-136 (row-tail property; see
also C. Kimberling, "The Zeckendorf array equals the Wythoff array", Fib. Quart. 33 (1995) 3-8, and the Wikipedia
article "Wythoff array"). Product structure: P. Arnoux, Appl. Math. Lett. 2 (1989) 319-320; OEIS A357097 (Munn,
2022). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

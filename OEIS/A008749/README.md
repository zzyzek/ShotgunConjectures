# OEIS A008749: a(n+2) is the first index where the minimal polyiamond perimeter reaches n + 4

**Source.** [A008749](https://oeis.org/A008749) (offset 0): expansion of (1+x^6)/((1-x)(1-x^2)(1-x^3)). Comment by
Winston C. Yang (Feb 05 2002): "Conjecture: For n >= 1, A067628(a(n+2)) appears for the first time in A067628."
[A067628](https://oeis.org/A067628) is the minimal perimeter of a polyiamond with T triangles; its FORMULA section
gives the Harary-Harborth (1976) value 2*ceiling((T + sqrt(6T))/2) - T. (OEIS text, CC BY-SA 4.0, checked
2026-11-06.)

**Reading.** "A067628(a(n+2)) appears for the first time" at index a(n+2): no T < a(n+2) has the same A067628
value. The entry's second sentence ("is the first T such that ... is a(n+2)") mixes index and value; the reading
proved here is the stronger one: A067628(a(n+2)) = n + 4 and a(n+2) is the least T with A067628(T) = n + 4.

**Result.** True for every n >= 1, given the Harary-Harborth formula.

**Argument.** Write p(T) = 2*ceil((T + sqrt(6T))/2) - T. For T >= 1 and v >= 2, p(T) = v iff v ≡ T (mod 2) and
v - 2 < sqrt(6T) <= v, i.e. (v-2)^2 < 6T <= v^2. Multiplying the g.f. out gives a(n+6) = a(n+5) + a(n+4) -
a(n+2) - a(n+1) + a(n) + [n = 0], and by induction 6 a(N) = N^2 + e(N mod 6) with e = 12, 5, 8, 9, 8, 5, and
a(N) ≡ N (mod 2), for N >= 1. Put N = n + 2 >= 3, A = a(N), v = n + 4 = N + 2. Then v ≡ A (mod 2),
(v-2)^2 = N^2 < 6A and 6A <= N^2 + 12 <= (N+2)^2, so p(A) = v. If T < A and p(T) = v, then T ≡ v ≡ A (mod 2),
so T <= A - 2 and 6T <= N^2 + e - 12 <= N^2 = (v-2)^2, a contradiction (T = 0 has p(0) = 0).

**Evidence.**
- Lean (Mathlib): [`A008749_mathlib.lean`](A008749_mathlib.lean). Definitions: `a` (recurrence),
  `p T = 2 ⌈(T + √(6T))/2⌉ - T`. Theorems: `A008749_gf` (mk a * (1-X)(1-X^2)(1-X^3) = 1 + X^6, so `a` is the
  entry's sequence), `six_a`, `p_eq_iff`, `A008749_first` (for n >= 1: p(a(n+2)) = n + 4 and p(T) ≠ n + 4 for all
  T < a(n+2)).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: propext, Classical.choice, Quot.sound.
  No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): the conjecture for n <= 398 from the formula; the formula
  against the A067628 b-file (T <= 10000); brute-force minimal perimeter over all polyiamonds (edge-connected
  triangle sets) for T <= 11, independent of Harary-Harborth.
- Outside Lean: the Harary-Harborth theorem that A067628(T) = p(T) (F. Harary, H. Harborth, Extremal animals,
  J. Combin. Inform. System Sci. 1 (1976) 1-8; also W. C. Yang, R. R. Meyer, Maximal and minimal polyiamonds,
  UW-Madison report 02-03, 2002). Formalising it needs the strip bound P >= r1 + r2 + r3, a count of the
  triangles in a three-band hexagon, and an optimal construction for every T; not attempted.

**Review level.** `lean-proof` (given Harary-Harborth).

**Prior art.** Checked 2026-11-06. The entry still marks it "Conjecture". Yang-Meyer (2002) determine the minimum
perimeter and the maximum number of triangles for a given perimeter, but the first-occurrence statement was not
found stated or proved there (abstract checked) or by web search. Not in google-deepmind/formal-conjectures (no
008749 or 067628 file in the tree at HEAD) or otoi-lab/oeis-lean-proofs.

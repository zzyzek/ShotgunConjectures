# OEIS A214970: L(2k-1) and L(2k)+1 divide their base-φ → base-φ² images

**Source.** OEIS [A214970](https://oeis.org/A214970): integers n dividing f(n), where f is the
change-of-base function of A214969 with b = φ and c = φ² (write n in base φ by the greedy
algorithm, n = sum d_i φ^i, then f(n) = sum d_i φ^(2i)). Conjecture (Kimberling, 2012): "L(2k-1)
and L(2k)+1 are terms of the sequence, for all positive integers k, where L=A000032 (Lucas
numbers)." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** The greedy base-φ expansion of an integer is its standard representation (digits
0/1, finitely many, no two adjacent 1s), which is unique (Bergman 1957). Using φ - φ^(-1) = 1 and
L(m) = φ^m - φ^(-m) for odd m:
sum_{j=-(k-1)}^{k-1} φ^(2j) = (φ^(2k-1) - φ^(-(2k-1)))/(φ - φ^(-1)) = L(2k-1). The digits sit at
even positions only, so this is the standard representation of L(2k-1), and
f(L(2k-1)) = sum φ^(4j) = (φ^(4k-2) - φ^(-(4k-2)))/(φ^2 - φ^(-2)) = F(4k-2) = F(2k-1) L(2k-1),
using φ^2 - φ^(-2) = √5. Likewise L(2k) + 1 = φ^(2k) + 1 + φ^(-2k) is a standard representation
for k ≥ 1, and f(L(2k)+1) = φ^(4k) + 1 + φ^(-4k) = L(4k) + 1 = L(2k)^2 - 1 =
(L(2k) - 1)(L(2k) + 1).

**Evidence.**
- `certificate/a214970_check.py` (scan): exact Z[φ] greedy expansion; reproduces the OEIS terms
  below 400 and confirms both families for k ≤ 12 (re-run for this write-up).
- Lean (Mathlib): [`A214970_mathlib.lean`](A214970_mathlib.lean) proves `A214970_unique` (standard base-φ representations, finite exponent sets with no two consecutive, are unique: Bergman's uniqueness) and `A214970_main`: for k >= 1, {2j : |j| <= k-1} is a standard representation of L(2k-1) with f-value L(2k-1)·F(2k-1), and {-2k, 0, 2k} one of L(2k)+1 with f-value (L(2k)+1)(L(2k)-1). The greedy step is covered by the next item.
- Lean (Mathlib), added: `A214970_greedy_main` in the same file formalises the greedy base-φ algorithm of the OEIS definition (largest power φ^i ≤ x, subtract, stop at 0) and proves f(L(2k-1)) = L(2k-1)·F(2k-1) and f(L(2k)+1) = (L(2k)+1)(L(2k)-1) for every k ≥ 1; `A214970_greedy_std` shows the greedy algorithm on a standard representation takes exactly its exponents. Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).

**Prior art.** Partly known. [OEIS A214970](https://oeis.org/A214970) (fetched 2026-11-04) still states the conjecture. The sister [A214971](https://oeis.org/A214971) has M. Dekking's 2019 proof of the companion statement, which supplies the base-phi representations; the divisibility step is not there. Searched: entry, OEIS cross-reference search, edit history, A214971 and its links. Worth an OEIS comment. (Prior-art review 2026-11-04.)

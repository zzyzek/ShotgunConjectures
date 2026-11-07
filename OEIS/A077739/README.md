# OEIS A077739 / A077740: a(n) = 0 exactly for n = 11, 17, 19

**Source.** [A077739](https://oeis.org/A077739) (offset 1), Amarnath Murthy, Nov 20 2002: "Smallest multiple of n
beginning and ending in n and having a digit sum of n, or 0 if no such number exists." Comment: "Conjecture: a(n) = 0
if and only if n is 11, 17 or 19." [A077740](https://oeis.org/A077740) is A077739(n)/n with the same conjecture
(Ray Chandler, Sep 05 2003). (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** N is admissible for n when n | N, the decimal string of N starts with that of n and ends with it
(overlap allowed, so N = n counts for n ≤ 9), and the digit sum of N is n. This reading reproduces the data of
A077739 for n ≤ 40 (certificate/brute.py).

**Result.** True. For n ≥ 1 an admissible N exists iff n ∉ {11, 17, 19}; so A077739(n) = 0 and A077740(n) = 0 iff
n ∈ {11, 17, 19}.

**Argument.** Write ds for the decimal digit sum.
- n = 19. N contains the digits 1, 9 at both ends. If the two copies of "19" do not overlap, ds(N) ≥ 20. They cannot
  overlap in one digit (9 ≠ 1); full overlap gives N = 19 with ds = 10.
- n = 17. As for 19, N = 17·10^(k+2) + 100·c + 17 where c has digits summing to 1 (the middle part), so c = 10^j.
  Then 17 | 100·10^j, impossible.
- n = 11. The two lowest digits of N are 1, 1, and ds(N) = 11, so the remaining digits sum to 9. The alternating
  digit sum of N equals that of the remaining digits, an odd number in [−9, 9], so it is not divisible by 11.
- n ≥ 63, construction. Let s = ds(n), r = n − 2s. By pigeonhole, 10^(i+P) ≡ 10^i (mod n) for some i and P ≥ 1. Let
  q = n / gcd(n, 10^i), so n | 10^i·q. Pick V = q·(m0 + 9k) with V ≡ r (mod 9) (possible since r ≡ −n (mod 9) and
  q | n) and r < V ≤ r + 18q; write V − r = 9y and y = 11z + v with v ≤ 10. Put u = r − v − z (≥ 0 because
  s ≤ 9 + n/10 and n ≥ 63). Let M = 10^i·Σ_t 10^(3P·t)·b_t where the blocks b_t are u copies of 1, v copies of 10 and
  z copies of 100. Each block has 3P ≥ 3 digits, so ds(M) = u + v + z = r, and modulo n,
  M ≡ 10^i·(u + 10v + 100z) = 10^i·V ≡ 0. Finally N = n + 10^D·(M + 10^M·n) (D = number of digits of n) begins and
  ends with n, is divisible by n, and has digit sum 2s + r = n.
- 1 ≤ n ≤ 62, n ∉ {11, 17, 19}: explicit witnesses (certificate/witnesses.txt), the least multiple for n ≤ 49 and
  n = 56, 58, 59, and a digit-DP witness of the form n·10^(L+D) + mid·10^D + n otherwise.

**Evidence.**
- Lean (Mathlib): [`A077739_mathlib.lean`](A077739_mathlib.lean). `A077739_Good n N` is the definition above stated
  with `Nat.digits` (prefix/suffix of the little-endian digit list); `A077739 n` is `Nat.find` or 0, `A077740 n` is
  `A077739 n / n`. Main theorems `A077739_eq_zero_iff` and `A077740_eq_zero_iff`: for n ≥ 1, the value is 0 iff
  n = 11 ∨ n = 17 ∨ n = 19. Supporting: `A077739_exists_good_iff`, `A077739_construct` (n ≥ 63),
  `A077739_not_good_11`, `A077739_not_good_17`, `A077739_not_good_19`.
- Check: `tools/leancheck-mathlib.sh`, OK, no warnings; axioms propext, Classical.choice, Quot.sound; no sorry, no
  native_decide.
- certificate/brute.py (least multiples for n ≤ 40, match the OEIS data), certificate/witness_dp.py,
  certificate/witnesses.txt.
- Outside Lean: none for the claim. Not verified in Lean: that the listed OEIS values are the least admissible
  multiples.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: OEIS entries (still "Conjecture"), web search, google-deepmind/formal-conjectures
(no file for 77739/77740), otoi-lab/oeis-lean-proofs (no file). No proof found.

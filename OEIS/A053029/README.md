# OEIS A053029 and A053031: which m have 4 (resp. 1) zeros in the Fibonacci numbers mod m

**Source.** [A053029](https://oeis.org/A053029) "Numbers with 4 zeros in Fibonacci numbers mod m" and
[A053031](https://oeis.org/A053031) "Numbers with 1 zero in Fibonacci numbers mod m" (Henry Bottomley, Feb 23 2000).
Conjectures in the entries: A053029, "m is on this list iff m is an odd number all of whose factors are on this
list or m is twice such an odd number"; A053031, the same with "2 or 4 times such an odd number". (OEIS text,
CC BY-SA 4.0, revisions #33 and #41 of Jun 11 2026, checked 2026-11-06.)

**Reading.** The number of zeros is counted in one Pisano period (OEIS A001176). "Factors" is read as prime
factors (reading it as all divisors other than 1 gives the same statement for m >= 3; the literal "all factors"
including m itself makes the statement circular). Under this reading the A053029 statement fails vacuously at
m = 1 and m = 2 (1 has no prime factors, 2 = 2 * 1, but both have one zero), so it is proved for m >= 3. The A053031
statement holds for every m >= 1.

**Result.** Both conjectures are true (A053029 for m >= 3). Known: B. Benfield and O. Lippard, *Connecting zeros in
Pisano periods to prime factors of K-Fibonacci numbers*, Fibonacci Quart. 63 (2025) 240-258 (arXiv:2407.20048),
Theorems 2.9-2.12, from results of Vinson, Wall, Renault. Reproved here in Lean.

**Argument.** Let alpha(m) be the rank of apparition (least n > 0 with m | F_n) and u = F_{alpha+1} mod m.
1. m | F_n iff alpha | n (F_gcd(a,b) = gcd(F_a, F_b)), and F_{j alpha + r} ≡ u^j F_r. So the Pisano period is
   alpha times the order of u, and the number of zeros per period equals ord_m(u).
2. Cassini gives u^2 ≡ (-1)^alpha. Hence for m >= 3: 4 zeros iff alpha(m) is odd; otherwise u^2 ≡ 1.
3. If u ≡ 1 (one zero) and m >= 3, then alpha = 2h with h odd: from F_{2h} = F_h L_h and
   F_{2h+1} - (-1)^h = F_h L_{h+1} with consecutive Lucas numbers coprime, h even would give m | F_h.
4. Divisors: alpha(d) | alpha(m) and u_m ≡ u_d^{alpha(m)/alpha(d)} (mod d). With alpha(m) ≡ 2 (mod 4) this forces
   u_d ≡ 1 for every divisor d >= 3 (an odd alpha(d) would give u_m ≡ -1 mod d). Since alpha(4) = 6 and
   (alpha(8), u_8) = (6, 13), four zeros exclude 4 | m and one zero excludes 8 | m.
5. Converse by induction over coprime prime-power factors. p^j | F_N implies p^(j+1) | F_{pN}, and
   (F_N, F_{N+1}) ≡ (0, 1) mod p^j implies the same mod p^(j+1) at pN (from F_{kN} ≡ k F_N F_{N+1}^(k-1) and
   F_{kN+1} ≡ F_{N+1}^k mod F_N^2). Odd indices N with m | F_N (A053029) multiply; indices N ≡ 2 (mod 4) with
   (F_N, F_{N+1}) ≡ (0, 1) (A053031) combine as 2AB from 2A and 2B. Step 2 and the order of u then give the count.

**Evidence.**
- Lean (Mathlib): [`A053029_mathlib.lean`](A053029_mathlib.lean). `zeros m` = number of n in (0, pisano m] with
  m | fib n, `pisano m` = least k > 0 with F_{n+k} ≡ F_n (mod m) for all n. Main theorems `A053029_conj` (m >= 3)
  and `A053031_conj` (m >= 1), stated with prime factors exactly as in the Reading; `zeros_one`, `zeros_two` for
  the A053029 edge cases. Route lemmas: `dvd_F_iff`, `shift`, `u_sq`, `zeros_spec`, `zeros_eq_four_iff`,
  `alpha_mod_four`, `zeros_one_of_dvd`, `lift_zero`, `lift_good`, `exists_odd_zero`, `exists_good`. Check:
  `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): zeros per period for m <= 3000 by direct iteration; both
  characterizations hold with no mismatch, and the data terms of both entries are reproduced.
- Outside Lean: none. Not verified in Lean: agreement of `zeros` with the OEIS data terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Benfield and Lippard (cited above, listed in both entries' references) prove
both conjectures, noting the same circularity of "factors". No Lean proof found: not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

# OEIS A227784 and A227781: -1 as a sum of fourth powers / squares mod n

**Source.** [A227781](https://oeis.org/A227781) "Least number of squares which add to -1 mod n" and
[A227784](https://oeis.org/A227784) "Least number of fourth powers which add to -1 mod n" (both offset 1,
Charles R Greathouse IV, 2013). Conjectures in the entries:
- A227781: "a(n) = 4 if and only if n is divisible by 8 and a(n) = 3 if and only if n is 4 mod 8."
- A227784: "a(n) = 15 if n = 9 mod 16 and a(n) = 7 if n = 8 mod 16, otherwise a(n) <= 4."
(OEIS text, CC BY-SA 4.0, checked 2026-11-06; the history shows no change to either conjecture.)

**Reading.** A227784 as printed is false: a(9) = 2 (1^4 + 2^4 = 17 = -1 mod 9), and the b-file has a(n) = 15
exactly for n = 0 mod 16 (n <= 10000) while the n = 9 mod 16 values lie in 1..4. Fourth powers mod 16 are 0, 1,
so "the associated lower bounds are obvious" fits n = 0 mod 16 only. We read "9 mod 16" as a typo for "0 mod 16"
and prove that version; the literal version is refuted separately.

**Result.** For n >= 1:
- A227781: a(n) = 4 iff 8 | n; a(n) = 3 iff n = 4 (mod 8); a(n) <= 2 otherwise. True as stated.
- A227784: a(n) = 15 if n = 0 (mod 16), a(n) = 7 if n = 8 (mod 16), a(n) <= 4 if 8 does not divide n.
  True with the corrected residue; false as printed (n = 9).

**Argument.** Let r_d(n) be the least k with -1 a sum of k d-th powers in Z/nZ.
1. *Padding and CRT.* 0 is a d-th power, so a representation with k terms gives one with any m >= k terms. If
   gcd(m, n) = 1 and -1 is a sum of k d-th powers mod m and mod n, the CRT ring isomorphism
   Z/mn = Z/m x Z/n gives one mod mn. Hence r_d(mn) = max(r_d(m), r_d(n)) for coprime m, n, and r_d(m) >= r_d(m')
   when m' | m (reduce mod m').
2. *Odd prime powers.* For an odd prime p: -1 is a sum of two squares mod p (Mathlib `ZMod.sq_add_sq`). For fourth
   powers, the set A of fourth powers mod p (with 0) has |A| >= 1 + (p-1)/4, since x -> x^4 is at most 4-to-1 on
   nonzero residues; Cauchy-Davenport gives |A+A+A+A| >= min(p, 4|A| - 3) = p, so -1 is a sum of four fourth
   powers mod p. Not every term is 0 (since -1 != 0), so some term y has p not dividing d*y^(d-1) (d = 2, 4). Hensel
   lifting of that one variable (y -> y + p^j s with s = -t u, where u*d*y^(d-1) + v*p = 1) gives a representation
   with the same number of terms mod every p^j. With step 1: r_2(m) <= 2 and r_4(m) <= 4 for odd m.
3. *Powers of 2.* Squares: mod 2, 1 = 1^2; mod 4, -1 = 3 needs three squares (squares are 0, 1) and has them;
   mod 8, squares are 0, 1, 4 and no three sum to 7; for 8 | n, n - 1 is a sum of four squares (Lagrange).
   Fourth powers: mod 2, 4, 8, 16 they are 0, 1, so -1 needs 1, 3, 7, 15 of them, and 1, 3, 7 ones suffice mod 2,
   4, 8. For 2^e with e >= 4: there is an odd y with y^4 = -15 mod 2^e (e = 4: y = 1; if y^4 + 15 = 2^e t with t odd,
   replace y by y + 2^(e-2)), so -1 = 14*1 + y^4.
4. Combining 2 and 3 with step 1 gives every claimed value; the lower bounds come from reducing mod 4, 8 or 16.

**Evidence.**
- Lean (Mathlib): [`A227784_mathlib.lean`](A227784_mathlib.lean). `IsRep d n k := ∃ x : Fin k → ZMod n,
  ∑ i, x i ^ d = -1`; `a n := sInf {k | IsRep 2 n k}` (A227781), `b n := sInf {k | IsRep 4 n k}` (A227784).
  Main theorems `A227784.A227781_conjecture : 0 < n → (a n = 4 ↔ 8 ∣ n) ∧ (a n = 3 ↔ n % 8 = 4)`,
  `A227784.A227781_le_two`, `A227784.A227784_corrected : 0 < n → (n % 16 = 0 → b n = 15) ∧ (n % 16 = 8 → b n = 7)
  ∧ (n % 8 ≠ 0 → b n ≤ 4)`, `A227784.A227784_literal_false`. Route: `isRep_mul` (CRT), `isRep_of_dvd`,
  `base2`, `base4` (Cauchy-Davenport `ZMod.cauchy_davenport`), `lift_step`, `lift_pow`, `rep_odd`
  (`Nat.recOnPrimeCoprime`), `two_adic`, `lower_count`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings;
  axioms propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): brute force for n <= 600 agrees with both b-files
  ([`b227781.txt`](certificate/b227781.txt), [`b227784.txt`](certificate/b227784.txt)) and with the rules above.
  The b-files (n <= 10000) satisfy the rules for every n.
- Outside Lean: none. Not verified in Lean: agreement of `a`, `b` with the OEIS data.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The level (Stufe) of Z/nZ is determined in H. N. Ramaswamy, R. Siddaramu,
"On the Stufe, unit Stufe and Pythagoras number of the ring of integers modulo n", Adv. Stud. Contemp. Math. 20
(2010) 373-388 (cited in D. W. Hoffmann, "Levels of rings - a survey", Banach Center Publ. 108 (2016)); this settles
A227781 (we did not read the paper itself). Higher levels of Z/p^l Z are determined by E. Becker, M. del P. Canales
(1999), and Parnami-Agrawal-Rajwade (1986) show the 4-power level of Q_2 is 15; with CRT these give A227784
(corrected). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs. The Lean proofs are ours.

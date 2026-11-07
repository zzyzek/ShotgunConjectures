# OEIS A219033: the sequence is infinite; the 6*A185208(n) ratio conjecture is false

**Source.** [A219033](https://oeis.org/A219033) (Jon Perry, 2012): numbers k such that k = x + y,
sigma_1(k) = sigma_1(x) + sigma_1(y) and sigma_2(k) = sigma_2(x) + sigma_2(y). Five conjectures in the entry: the
sequence is infinite; it has only even terms; the parts are even; no term satisfies the sigma_3 equality; "With the
lower partition as 6*A185208(n) and the upper partition 214/3 = 71.3333... of this, then the equalities are
satisfied." (OEIS text, CC BY-SA 4.0, revision #36 of Feb 24 2026, checked 2026-11-06.) A185208: numbers with no
divisor d > 1 such that d + 1 is a prime power.

**Result.**
1. Conjecture 1 is true: 434m is a term for every m coprime to 2*3*7*31*107 (parts 428m and 6m).
2. Conjecture 5 is false: 107 is in A185208, but x = 6*107 = 642, y = 428*107 = 45796 gives
   sigma_1(46438) - sigma_1(45796) - sigma_1(642) = 749 != 0 (and the sigma_2 difference is 240429).
3. Conjectures 2-4 (even terms, even parts, no sigma_3 solution) remain open; they hold for k <= 16100.

**Argument.** 434 = 2*7*31, 428 = 4*107, 6 = 2*3. sigma_1: 768 = 756 + 12; sigma_2: 240500 = 240450 + 50. If m is
coprime to 4*3*7*31*107 then m is coprime to 434, 428 and 6, and multiplicativity of sigma_k gives
sigma_k(434m) = sigma_k(434)sigma_k(m) = (sigma_k(428) + sigma_k(6))sigma_k(m) = sigma_k(428m) + sigma_k(6m) for
k = 1, 2. The m = 278628t + 1 are pairwise distinct and coprime to 278628, so the sequence is infinite. For m = 107
the factor 107 divides 428, sigma_1(428*107) = sigma_1(4)sigma_1(107^2) = 7*11557 = 80899, sigma_1(642) =
12*108 = 1296, sigma_1(46438) = 768*108 = 82944, and 82944 - 80899 - 1296 = 749. The first-12 partitions quoted in
the entry are the m in A185208 below 107; A185208 contains every prime other than 2 and the Mersenne primes, and
107 is the first member sharing a factor with 428.

**Evidence.**
- Lean (Mathlib): [`A219033_mathlib.lean`](A219033_mathlib.lean). `InSeq k` is the OEIS definition with
  Mathlib's `σ`; `InA185208` is the A185208 definition. Main theorems `A219033.A219033_infinite :
  {k | InSeq k}.Infinite` and `A219033.A219033_ratio_fails : InA185208 107 ∧ σ 1 (434*107) ≠ σ 1 (428*107) +
  σ 1 (6*107)`; also `A219033_family`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext,
  Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/family.py`](certificate/family.py): family check for m <= 3000, the m = 107 differences, 107 in
  A185208, and brute force for k <= 16100 (all 10 terms match the data; no odd term, no odd part, no sigma_3
  solution); exit 0, 32 s.
- Outside Lean: none for results 1 and 2. Conjectures 2-4 are not proved.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry gives Johnson's 2012 remark that the 214/3 ratio is not used for
a(67) but no proof of infinitude and no note that the ratio conjecture fails. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

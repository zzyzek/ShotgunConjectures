# Coman P066: (P + 5^m) prime conjectures for Poulet numbers

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes*
(2013), Part four (open problems), problem 66, restating conjectures 126-129 of Part one. Paraphrase: (1) every
Poulet number P with 3, 5 not dividing P has m >= 1 with (P + 5^m)/6^n prime or a prime power; (2) every Poulet
P with 5 | P, 3 not dividing P, has m with (P + 5^m)/30 prime; (3) every Poulet P with 15 | P has m with
(P + 5^m)/10 prime; (4) apart from "definable exceptions", every n not divisible by 5 has m with 6n - 5^m prime
or 1.

**Reading.** In (1), n is any exponent with 6^n | P + 5^m (the claim fails for every such n below, so the
choice of n does not matter).

**Result.**
- (1) False, non-constructively (new here). For every P = a (mod M) with
  a = 164743819436130905311195649881, M = 197386120142055051194076523980 = 4·3·5·13·313·17·11489·31·7·601·
  390001·19·829·5167, every m and every admissible n, (P + 5^m)/6^n is not a prime power. The class is coprime
  (gcd(a, M) = 1), so it contains infinitely many Carmichael numbers (T. Wright, Bull. London Math. Soc. 45
  (2013) 943-952), which are Poulet numbers with 3, 5 not dividing P. No explicit P is known.
- (2) False: see [COM/C127](../C127/README.md) (covering plus Larsen 2025).
- (3) False: see [COM/C128](../C128/README.md).
- (4) Ill-posed: the exceptions are not defined; 113 n below 3000 have no such m (scan record COM-C129).

**Argument for (1).** P = 1 (mod 4) gives P + 5^m = 2 (mod 4), so n <= 1. For n = 0, P + 5^m = 2·u with u odd
and u > 1, not a prime power. For n = 1, 3 | P + 5^m forces m odd (P = 1 mod 3). Two disjoint coverings of the
odd m: m = 1 (4), 3 (8), 7 (16), 15 (16) with q = 13, 313, 17, 11489, and m = 0 (3), 1 (6), 5 (12), 11 (24),
2 (9), 5 (9), 17 (18) with q = 31, 7, 601, 390001, 19, 829, 5167 (q | 5^ord - 1 with the stated order). P = -5^r
(mod q) on each class, so for odd m one prime from each covering divides (P + 5^m)/6; two distinct primes, so not
a prime power.

**Evidence.**
- Lean (Mathlib): [`P066_mathlib.lean`](P066_mathlib.lean). `P066_part1`: for P % M = a and 6^n | P + 5^m,
  `¬ IsPrimePow ((P + 5^m) / 6^n)`. Finite facts (`cover1_ok`, `cover2_ok`, `ord1`, `cls1`, `disjoint`, ...) by
  `decide`; `class_facts` gives gcd(a, M) = 1. Axioms propext, Classical.choice, Quot.sound.
- `certificate/cover_check.py` (output `check.log`): rebuilds a by CRT, checks the coverings and spot-checks
  members of the class for m <= 300.
- Outside Lean: Wright's theorem (Carmichael numbers in every coprime progression). For (2) Larsen's theorem,
  see C127. Nothing else.

**Review level.** lean-proof of the covering; citation for Wright.

**Prior art.** Checked 2026-11-08: the scan records for COM-C126..C129; Wright 2013; Larsen arXiv:2504.09056.
The double-covering argument for (1) was not found stated. (1) was earlier recorded as open (no small failure has
a single covering because prime powers are allowed; two disjoint coverings remove that).

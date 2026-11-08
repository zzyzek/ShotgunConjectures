# COM-C126 (Coman, Conjecture 126): false (non-constructively, via Wright's theorem); P = 15709 settled at m = 749

**Source.** M. Coman, *Two hundred conjectures and one hundred and fifty open problems on Fermat pseudoprimes*
(2013), Conjecture 126 (also Open Problem 66, Conjecture 1): for every Poulet number P not divisible by 3 or 5
there are m, n >= 1 such that (P + 5^m)/6^n is a prime or a prime power (paraphrased). Examples given: 341
(m = 2, n = 1: 61), 1387 (m = 3, n = 3: 7), 1729 (m = 1, n = 1: 17^2).

**Reading.** 6^n must divide P + 5^m; since P is odd, this needs m odd when P = 1 (mod 3) and m even when
P = 2 (mod 3). The scan found three Poulet numbers with no m < 60: 13747, 14491, 15709.

**Result.** False, non-constructively. The same statement is part (1) of Coman's Open Problem 66; [COM/P066](../P066/README.md) proves in Lean that for every P in an explicit coprime residue class modulo M = 197386120142055051194076523980 and all m, n with 6^n | P + 5^m, (P + 5^m)/6^n is not a prime power (covering argument). Wright's theorem (Bull. London Math. Soc. 45 (2013)) puts infinitely many Carmichael numbers, hence Poulet numbers prime to 15, in that class. No explicit counterexample P is known.

Data for the three small hard cases (kept from the first write-up): Partial. P = 15709: (15709 + 5^749)/6 is prime (523 digits), and no m <= 748 works. P = 13747 and
P = 14491: no m <= 4000 (any n) gives a prime or prime power. No covering set with moduli of lcm up to 10^6
exists for these two (about 15-21% of admissible m uncovered), so the conjecture is expected to hold but is not
reached.

**Argument.** Direct search: for each m, divide out 6 while possible and test every quotient for being a
probable prime or a perfect power of one (PARI ispseudoprime, ispower); certificate/c126.gp (m <= 600),
c126b.gp (m <= 4000). The m = 749 value is proved prime by an ECPP certificate (PARI primecert, validated by
primecertisvalid; certificate/cert15709.txt).

**Evidence.** No Lean file. Outside Lean: the PARI searches (pseudoprime tests only rule values in as
candidates; the non-existence statements for m <= 4000 rest on ispseudoprime returning false, which is a proof of
compositeness), the ECPP certificate check in PARI, and the covering check (cover.py).

**Review level.** Searches run once; the prime certified.

**Prior art.** Coman's text, scan notes, web search; no later treatment found (checked 2026-11-08).

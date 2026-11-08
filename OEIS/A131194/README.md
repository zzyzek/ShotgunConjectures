# OEIS A131194, A133835: every seed's orbit merges with the main one

**Source.** [A131194](https://oeis.org/A131194): slowest increasing sequence of primes such that two neighbour
terms share at least three digits (counted with multiplicity), seed 101. [A133835](https://oeis.org/A133835): the
same with two digits, seed 11. Both entries list orbits of other seeds and conjecture: "for any initial seed,
sequence eventually merges with the first one." (OEIS text, CC BY-SA 4.0, cached entries, checked 2026-11-07.)

**Reading.** For s = 3 (resp. 2) and a prime p with at least s digits, next(p) is the least prime q > p whose
decimal digit multiset shares at least s elements with that of p. A seed's sequence is its orbit under next.
"Merges" means the two orbits have a common term (then they agree from there on).

**Result.** True for both s = 3 and s = 2, assuming only the prime number theorem in the form: for every ε > 0
there is x_0 with a prime in (x, (1 + ε)x] for all x ≥ x_0.

**Argument.** Write a D-digit number (D ≥ 9) as its top part k (first 8 digits, 10^7 ≤ k < 10^8) and its low part
(D - 8 digits). The block of k is the set of D-digit numbers with top part k; it is an interval of relative width
1/k ≥ 10^-8, so for D ≥ D_0 every block contains a prime (PNT). Let L_k be the largest prime in block k.

1. *Walking.* Consecutive primes in one block share the 8 top digits, so next(p) = nextprime(p) while that stays
   in the block. An orbit with a term in block k therefore contains every later prime of the block, ends the
   block at L_k, and continues with next(L_k), which depends only on k.
2. *Good blocks.* Write k = x9^r with x not ending in 9. If x has at least 4 digits, then k and k+1 agree in the
   first len(x) - 1 ≥ 3 positions, so the first prime of block k+1 shares ≥ 3 digits with L_k and the orbit
   moves to block k+1. Call such k good. A bad k has len(x) ≤ 3, hence r ≥ 5 trailing 9s.
3. *Bad blocks.* For bad c = x9^r: block c + 1000 has top part (x+1)0^(r-3)999 (or, if x is empty, the top part
   10000999 among (D+1)-digit numbers). It contains a prime (PNT) sharing three 9s with L_c, so next(L_c) lies in
   a block B(c) with c < B(c) ≤ c + 1000. No block in (c, c + 1000] is bad: its top part ends in at most three 9s.
4. *Merging.* Fix D_0 and the main orbit's first term above 10^{D_0}. From there the main orbit visits every
   block except the open ranges (c, B(c)) after bad blocks c. Any other orbit eventually has a term above
   10^{D_0}, in some block b. If the main orbit visits b, both contain L_b. Otherwise b lies in some (c, B(c));
   all blocks from b to B(c) are good, so the orbit walks block by block into B(c) and both contain L_{B(c)}.
   The same proof works for s = 2 (every step above gives at least 3 shared digits).

**Evidence.**
- Lean (Mathlib + `OpenProblemsLib.PNTApps` + vendored PNT+): [`A131194_mathlib.lean`](A131194_mathlib.lean).
  `A131194_merge`: every seed a ≥ 100 has next_3^[i] a = next_3^[j] 101 for some i, j; `A133835_merge`: the
  same for s = 2, seeds a ≥ 10, main seed 11; `merge_general` for any 1 ≤ s ≤ 3. `next s p` is the least
  prime q > p whose decimal digit multiset shares at least s elements with that of p. The Lean proof is a
  simplified form of the argument above: with L_j the largest prime below 10^(j+8), every orbit walks
  through L_j for all large j (a later prime of the same block, else a prime of block k + 1 when k does not
  end in 99999, else a prime of the top block 99999999, always shares 3 digits), so two orbits meet at
  L_j. The prime number theorem enters as `exists_prime_block` (from PNT+'s `prime_between`). Checked
  2026-11-08 with `tools/leancheck-mathlib.sh`: OK, axioms propext, Classical.choice, Quot.sound.
- [`certificate/merge.py`](certificate/merge.py): every prime seed below 10^4 merges with the main orbit, for
  s = 3 (latest merge point 10789) and s = 2 (latest 9973).
- Outside Lean: none.

**Review level.** `lean-proof` (both merge conjectures proved in Lean from the prime number theorem of PNT+).

**Prior art.** Checked 2026-11-07: both OEIS entries (conjecture still stated, entry says the main sequence
"presumably contains almost all primes"), formal-conjectures, oeis-lean-proofs: no proof found. The same
argument shows the main orbit contains all primes outside the ranges (c, B(c)), a set of relative density
tending to 0, which settles the "almost all primes" remark in the same sense.

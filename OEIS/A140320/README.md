# OEIS A140320: a(n) = 2n*3^(n-1) + 1

**Source.** [A140320](https://oeis.org/A140320) (offset 0), Vladimir Shevelev, May 26 2008: "a(n) =
A137576((3^n-1)/2)." Comment: "Conjecture. a(n)=2n*3^(n-1)+1." Here [A137576](https://oeis.org/A137576)(n) =
A002326(n)*A006694(n) + 1, with [A002326](https://oeis.org/A002326)(n) the multiplicative order of 2 mod 2n+1 and
[A006694](https://oeis.org/A006694)(n) the number of cyclotomic cosets of 2 mod 2n+1. (OEIS text, CC BY-SA 4.0,
A140320 revision #13 of Jun 28 2026, checked 2026-11-06.)

**Reading.** A006694 does not count the coset {0}: its data start 0, 1, 1, 2 (mod 3 the cosets are {0}, {1, 2}, and
the value is 1), with "a(0) = 0 by convention". So A006694(n) is the number of distinct sets {x*2^k mod 2n+1 : k >= 0}
with 1 <= x <= 2n. With this reading A137576(0..63) and A140320(0..12) match the entries' data.

**Result.** True for every n >= 0 (a(0) = 1).

**Argument.** Let m = 3^n, n >= 1, so (3^n-1)/2 is the index with 2*index + 1 = m.
1. *2 has order 2*3^(n-1) = phi(3^n) mod 3^n.* Its order divides phi(3^n) by Euler. 2^(3^(n-1)) = 2 mod 3 (odd
   exponent), so it is not 1. For n >= 2, 2^(2*3^(n-2)) - 1 = 4^(3^(n-2)) - 1 has 3-adic valuation
   v_3(4-1) + v_3(3^(n-2)) = n-1 by lifting the exponent, so it is not 1 mod 3^n.
2. *Cosets.* Write a nonzero x mod 3^n as 3^j*u with j < n, 3 not dividing u. Every element of the coset of x has
   valuation exactly j (multiplying by 2 and reducing mod 3^n does not change it, as j < n). By step 1 applied to
   3^(n-j), the powers of 2 run through all units mod 3^(n-j), so the coset of x is the set of all residues of
   valuation j, the coset of 3^j. Hence there are exactly n cosets, one per j = 0, ..., n-1.
3. a(n) = 2*3^(n-1) * n + 1. For n = 0, A002326(0) = 1 (order of 2 mod 1) and A006694(0) = 0, so a(0) = 1.

**Evidence.**
- Lean (Mathlib): [`A140320_mathlib.lean`](A140320_mathlib.lean). Definitions: `A002326 n = orderOf (2 : ZMod
  (2n+1))`, `coset m x = {x*2^k % m}`, `A006694 n` = `Set.ncard` of the set of cosets `coset (2n+1) x` with
  1 ≤ x < 2n+1, `A137576`, `A140320` as in the entries. Main theorem `OEIS140320.A140320_formula : A140320 n =
  2*n*3^(n-1) + 1` (all n). Route: `ord_two` (step 1, LTE via `padicValNat.pow_sub_pow`), `gen` (powers of 2 are
  all units mod 3^r), `coset_eq`, `val_mod`, `coset_inj` (step 2), `A006694_pow3`, `A002326_pow3`. Check:
  `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): A137576(0..63) from the definitions matches the entry data;
  A140320(0..13) equals 2n*3^(n-1)+1 and the data.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The result is immediate from known facts and is effectively recorded in OEIS:
- A137576 states, without proof, "if p is an odd prime then a((p^k-1)/2)=1+k*phi(p^k)"; for p = 3 this is the
  conjecture.
- A006694 carries Shevelev's conjecture A006694((3^n-1)/2) = n, marked correct by Joerg Arndt (2019) via the
  factorisation of (x^(3^n)-1)/(x-1) over GF(2).
- 2 is a primitive root mod 3^n (textbook).
- Aside: the general A137576 formula needs ord(2, p^k) = p^(k-1) ord(2, p). It fails at the Wieferich prime
  p = 1093, k = 2: A137576((1093^2-1)/2) = 364*3282 + 1 = 1194649, not 1 + 2*phi(1093^2) = 2387113
  ([`certificate/wieferich.py`](certificate/wieferich.py)).

A140320 still shows the conjecture. Searched: google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/140320.lean`),
otoi-lab/oeis-lean-proofs (nothing on 140320 or 137576), web (Shevelev's overpseudoprime papers, arXiv:0806.3412,
treat the general A137576 identity, not this case explicitly).

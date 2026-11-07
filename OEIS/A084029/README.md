# OEIS A084029: only one term is zero

**Source.** [A084029](https://oeis.org/A084029) (Amarnath Murthy, May 24 2003): triangle whose n-th row contains the
first n n-digit multiples of n with digit sum n, padded with 0s. "Conjecture: Only one term is zero." (OEIS text,
CC BY-SA 4.0, checked 2026-11-07.)

**Reading.** The zero is in row 2 (20 is the only 2-digit even number with digit sum 2). The conjecture says: for
every n >= 3 there are at least n n-digit multiples of n with digit sum n.

**Result.** True.

**Argument.** Write a solution as a digit vector (c_0, ..., c_(n-1)), c_i in [0, 9], c_(n-1) >= 1, sum c_i = n,
sum c_i 10^i == 0 (mod n). Write n = g m, g = 2^a 5^b, gcd(m, 10) = 1, e = a + b (so g | 10^e), r = ord_m(10).
1. *n <= 130:* direct count (digit DP): every row 3..130 has at least n solutions.
2. *One solution with digits <= 2 (every n).* Two copies of each 10^i, i < n, are 2n integers; by
   Erdos-Ginzburg-Ziv some n of them sum to a multiple of n. The sum has digits in {0,1,2}, digit sum n, at most n
   digits; shifting it left gives an n-digit solution N0 with digits <= 2.
3. *Case 2r <= n - 1 - e* (this holds whenever g > 1 and n >= 8, and whenever g = 1 and r <= (n-1)/2). Cut
   [e, n-1) into blocks of length r starting at e (blocks 0 and 1 are complete). Moving one unit of N0 from position
   i >= e to i + r or i - r (staying in [e, n-1)) keeps the residue mod n (10^r == 1 mod m, and both powers are
   == 0 mod g) and the digit sum, and keeps the top digit. Let Z be the number of nonzero digits of N0 in [e, n-1);
   Z >= n/2 - e - 1. Sources in odd blocks move down by r (injective, into even blocks); sources in even blocks move
   up (block 0) or down (blocks >= 2) into odd blocks, injective after dropping one source from each colliding pair
   (i in block 0, i + 2r in block 2). One of the two families has a set A of at least Z/3 sources with distinct
   targets outside A. Each subset T of A gives a distinct solution (its digits on A identify T), so there are at
   least 2^(Z/3) >= 2^(n/6 - (e+1)/3) solutions, which is >= n for n >= 131 (e <= log2 n).
4. *Case g = 1, 2r > n - 1.* Then r = phi(n) (r divides phi(n) <= n - 1), so 10 generates (Z/n)^*; n = p^k with p
   odd, p != 3, 5. Let h = r/2 (10^h == -1) and t with 10^t == -2. For a set S of (n-3)/2 slots i in [0, n-1-h]
   containing n-1-h, the vector 2 e_0 + e_t + sum_{i in S} (e_i + e_(i+h)) has digit sum n, digits <= 4, top digit
   >= 1, and value == 2 - 2 + sum 10^i (1 + 10^h) == 0. Different S give different vectors (read off slots from the
   lowest position up). There are C(n-h-1, (n-5)/2) >= C((n-1)/2, 2) >= n of them for n >= 13.
So every row n >= 3 is full; row 1 is (1) and row 2 is (20, 0).

**Evidence.**
- Lean (Mathlib): [`A084029_mathlib.lean`](A084029_mathlib.lean), theorem `A084029.A084029_row_nonempty` (step 2:
  an n-digit multiple of n with digit sum n exists for every n >= 1, via Mathlib's `Int.erdos_ginzburg_ziv`).
  Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound.
- [`certificate/rowcount.py`](certificate/rowcount.py) with output [`certificate/rowcount130.txt`](certificate/rowcount130.txt):
  step 1 (n <= 130; only row 2 is short).
- [`certificate/brute_small.py`](certificate/brute_small.py): brute force reproduces the data (rows 1..7).
- [`certificate/construct_check.py`](certificate/construct_check.py): builds the step 3 and step 4 families for
  131 <= n <= 200 and checks every built vector (residue, digit sum, digits, top digit) and the counts.
- Outside Lean: the counting steps 3 and 4 (paper proof above, checked numerically for n <= 200) and the
  n <= 130 count (Python DP).

**Review level.** `rechecked` (paper argument re-derived and tested; the existence step is `lean-proof`).

**Prior art.** Checked 2026-11-07: the entry has data through row 8 and no b-file; "every n has a multiple with
digit sum n" is classical, the exact-length counting statement was not found; google-deepmind/formal-conjectures
and otoi-lab/oeis-lean-proofs local clones (2026-11-06): nothing.

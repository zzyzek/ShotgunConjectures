# OEIS A209860, A209861, A209862: A054429 commutes with the permutation A209861/A209862

**Source.**
- [A209862](https://oeis.org/A209862): "Conjecture: For all n, a(A054429(n)) = A054429(a(n)) ..." (revision #26, Sep 15 2021).
- [A209861](https://oeis.org/A209861) (inverse permutation): "Conjecture: For all n, A209861(A054429(n)) = A054429(A209861(n)) ..."
- [A209860](https://oeis.org/A209860) (fixed points): "Conjecture: for every a(n), also A054429(a(n)) is in the sequence. Conversely, if i is not in the sequence, then neither is A054429(i)."

All three by Antti Karttunen, Mar 24 2012; OEIS text, CC BY-SA 4.0; all still conjectures on 2026-11-06.

**Reading.** A209642(n) is given by the entry's Scheme loop (read n from the least significant bit; a 0-bit sends
(s, i) to (4s+1, 4i), a 1-bit to (2(s+i), 4i); start (0, 1)). A209641 is the same set of values in ascending order,
A209861 maps A209641 to A209642 (so A209861(n) is the position of A209642(n) in A209641, offset 0), and A209862 is its
inverse. A054429 has offset 1: A054429(n) = 3·2^k − 1 − n for 2^k ≤ n < 2^(k+1). The conjectures are read for n ≥ 1.

**Result.** True: A209861(A054429(n)) = A054429(A209861(n)) and A209862(A054429(n)) = A054429(A209862(n)) for all
n ≥ 1, and for i ≥ 1, i is a fixed point iff A054429(i) is.

**Argument.** Let g = A209642, and for n ≥ 1 let L = len(n) (binary length), K = pop(n) (number of 1-bits),
E = 2L − K, and tau(n) defined by tau(1) = 0, tau(2q+1) = tau(q), tau(2q) = 2^E(q) + tau(q).
1. *Closed form.* Induction on the loop: g(n) + 2^E = 2^(2L) + tau(n), with 2·tau(n) < 2^E. So
   2^(2L−1) ≤ g(n) < 2^(2L): g maps level L (2^(L−1) ≤ n < 2^L) into the 2L-bit numbers, and A209861 maps level L
   onto itself. (As words: g(n) is 1^K followed by the tokens "0" for a 1-bit and "01" for a 0-bit of n, LSB first.)
2. *Order on a level.* For n, n' on level L: fewer 1-bits gives a smaller g value; with equal popcount, g order =
   tau order. With equal popcount, tau(odd) < tau(even), and when the last bits agree the comparison passes to
   (n div 2, n' div 2).
3. *A054429 reverses the order.* A054429 keeps the level, sends popcount K to L + 1 − K, and satisfies
   A054429(2q) = 2·A054429(q) + 1, A054429(2q+1) = 2·A054429(q). It flips every bit below the leading one, so by step 2
   g(n) < g(n') iff g(A054429(n')) < g(A054429(n)). Step 2 also shows g is injective.
4. *Ranks.* A209861(n) = 2^(L−1) + r(n), r(n) = #{i on level L : g(i) < g(n)}. Reindexing by A054429 and step 3 give
   r(A054429(n)) = 2^(L−1) − 1 − r(n), which is the claim for A209861. A209861 is a bijection (injective, and maps
   each level into itself), so the claim passes to the inverse A209862 and to the fixed points A209860.

Wiseman's description of A209862 (Aug 2021 comment, verified there up to 2^15) follows from steps 1-2: within a row,
sets are sorted by size, then lexicographically. It is not formalised here.

**Evidence.**
- Lean (Mathlib): [`A209860_mathlib.lean`](A209860_mathlib.lean), namespace `A209860`. `A209642` = the Scheme loop,
  `A209861 n = Set.ncard {i | A209642 i < A209642 n}`, `A209862 = Function.invFun A209861`,
  `A054429 n = 3 * 2 ^ Nat.log 2 n - 1 - n`. Main theorems `A209861_conjecture`, `A209862_conjecture`,
  `A209860_conjecture` (all for n ≥ 1). Steps: `loop_closed`, `g_closed`, `tau_lt`, `g_bounds` (1);
  `g_lt_of_pop_lt`, `g_lt_iff_tau`, `tau_odd_lt_even` (2); `c_even`, `c_odd`, `pop_c`, `tau_c`, `g_c`, `g_inj` (3);
  `A209861_eq`, `rk_c`, `A209861_conj`, `A209861_inj`, `A209861_surj` (4).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms of every theorem at most propext,
  Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py) (arguments: the three b-files): from the Scheme loop, the rank
  definition reproduces the A209861 and A209862 b-files (n < 2^15) and the A209860 b-file terms below 2^15; the
  entry's A209641 membership test accepts exactly the values of A209642 below 4^8; the closed form of step 1 holds
  for n < 2^15; the conjecture holds for n < 2^15.
- Outside Lean: the reading that A209641 is exactly the ascending list of the values of A209642 (stated in the
  A209642 entry; checked numerically below 4^8 against the entry's membership test).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The three entries still list the conjectures; Wiseman's 2021 comment in A209862 is
itself labelled as verified up to 2^15, not proved. A209863 (number of fixed points per level) notes that the
conjecture would make its terms from a(2) on even. Web search (A209862, A209861, A054429, conjecture) found no proof.
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06).

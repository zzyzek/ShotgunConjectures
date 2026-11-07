# OEIS A225660: a(n) is odd for n > 9

**Source.** [A225660](https://oeis.org/A225660) (Clark Kimberling, 2013): number of nonrepeating vectors in the
counting procedure H(0) = binary digits of n, H(q+1) = F(H(q)), where F(S) = (f(0), ..., f(max S)) and f(i) is the
number of occurrences of i in S. Comment: "Conjecture: if n>9, then a(n) is odd." (OEIS text, CC BY-SA 4.0, revision
#14 of Dec 04 2016, checked 2026-11-06.)

**Reading.** a(n) = least i such that H(i) occurs again later; this reproduces the data (e.g. a(7) = a(9) = 0
because 111 and 1001 lie on a cycle).

**Result.** True: a(n) is odd for every n > 9.

**Argument.**
1. *Cycles.* The set C = {002, 011, 03, 1001, 111, 12, 201, 22} is closed under F and F^6 is the identity on C
   (cycles 12 -> 011 -> 12 and 22 -> 002 -> 201 -> 111 -> 03 -> 1001 -> 22). If the orbit of a vector meets C,
   then H(i) repeats iff H(i) is in C (a periodic H(i) equals F^{pT}H(i), which lies in C once the orbit is in C),
   so a(n) is the first time the orbit meets C.
2. *First step.* For n >= 1, F(bits) = (z, o), the numbers of 0s and 1s; for n >= 8, z + o >= 4 and o >= 1. For
   n > 9 the binary word of n is not in C (the members of C read as binary numbers are at most 9), so
   a(n) = 1 + (hitting time of C from (z, o)).
3. *Pairs return in an even number of steps.* For z != o with q = max(z, o): F(z, o) is the word of length q+1 with
   1 at positions z and o, and F^2(z, o) = (q-1, 2). For m >= 3: (m, m) -> 0^m 2 -> (m, 0, 1) -> 1 1 0^{m-2} 1 ->
   (m-2, 3). The intermediate words have length >= 6 or maximum >= 5, so they are not in C when max >= 5.
4. *Induction on max(z, o).* For pairs with z + o >= 4, o >= 1 and max <= 4 the hitting time is even (finite check).
   For max >= 5, step 3 reaches a pair with smaller max, still with sum >= 4 and o in {2, 3}, after 2 or 4 steps.
   So the hitting time from (z, o) is even and a(n) is odd.

**Evidence.**
- Lean (Mathlib): [`A225660_mathlib.lean`](A225660_mathlib.lean). `F`, `bits n` (binary digits, most significant
  first), `H n k = F^[k] (bits n)`, `Rep n i` (H n i occurs later) and `a n` (least i with `Rep n i`) follow the
  entry. Main theorem `A225660.A225660_odd : 9 < n → Odd (a n)`. Route: `C_closed`, `C_period`, `rep_iff` (step 1);
  `F_bits`, `len_bits`, `bits_not_C` (step 2); `F2_pair`, `F4_diag` (step 3); `base` (by `decide`), `pair_hit`
  (step 4). Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/explore.py`](certificate/explore.py): a(0..39) equal the data; hitting times of pairs; the cycle
  set C; a(n) odd for 10 <= n < 65536.
- Outside Lean: none. Not verified in Lean: agreement of `a` with the OEIS data terms.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry proves eventual 6-periodicity (Theorem 1, by induction on the maximum,
using the same pair moves as Lemmas 1-3) but leaves the parity as a conjecture; no later edit. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

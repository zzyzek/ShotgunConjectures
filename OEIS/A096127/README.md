# OEIS A096127: a(n) = n+1 exactly when n is a prime power

**Source.** [A096127](https://oeis.org/A096127) (offset 2), Amarnath Murthy, Jul 03 2004: "a(n) is the largest k
such that (n^2)!/(n!)^k is an integer." Comment: "Conjecture: a(n)=n+1 only when n is prime or a power of a prime.
[Verified for n=2..5000. - _Amiram Eldar_, Apr 06 2021]" (OEIS text, revision #13 of Apr 06 2021, checked
2026-11-06.)

**Result.** True. For n ≥ 2, a(n) ≥ n+1 always, and a(n) = n+1 if and only if n is a prime power.

**Argument.** Fix a prime p, write s(m) for the base-p digit sum of m, and use Legendre's formula
(p-1) v_p(m!) = m - s(m). Then (n!)^k divides (n^2)! iff for every prime p,
k (n - s(n)) ≤ n^2 - s(n^2).

1. *Digit sums.* s(a+b) ≤ s(a) + s(b), because a! b! divides (a+b)! (apply Legendre to both sides). Also
   s(p m) = s(m). Writing m = (m mod p) + p (m div p) gives s(mn) ≤ (m mod p) s(n) + s(m div p) s(n), so by
   induction s(mn) ≤ s(m) s(n); in particular s(n^2) ≤ s(n)^2. Finally 1 ≤ s(n) ≤ n for n ≥ 1, and s(n) = 1
   exactly when n is a power of p.
2. *k = n+1 always works.* With t = s(n), 1 ≤ t ≤ n: (n+1)(n-t) = n^2 - t^2 - (t-1)(n-t) ≤ n^2 - t^2 ≤
   n^2 - s(n^2).
3. *k = n+2 works when n is not a prime power.* Then n is not a power of p, so 2 ≤ t ≤ n and
   (n+2)(n-t) = n^2 - t^2 - (t-2)(n-t) ≤ n^2 - s(n^2).
4. *k = n+2 fails for n = p^m, m ≥ 1.* Here s(n) = s(n^2) = 1, and (n+2)(n-1) > n^2 - 1 for n ≥ 2.

Since (n!)^k | (n^2)! is downward closed in k, steps 2-4 give a(n) = n+1 iff n is a prime power.

**Evidence.**
- Lean (Mathlib): [`A096127_mathlib.lean`](A096127_mathlib.lean). `a n` is `Nat.findGreatest (fun k => n! ^ k ∣
  (n^2)!) ((n^2)!)`, the entry's definition (the predicate holds at n+1 ≤ (n^2)! and is downward closed, so the
  bound is harmless; this is proved in the file, not assumed). Main theorem `A096127_eq_succ_iff : 2 ≤ n →
  (a n = n + 1 ↔ IsPrimePow n)`; the conjecture as stated is `A096127_conjecture`. Route: `s_add_le`, `s_mul_le`,
  `s_eq_one`, `s_pow` (step 1), `dvd_iff_val` (divisibility prime by prime via `Nat.factorization`), `ineq_one`,
  `ineq_two`, `not_two` (steps 2-4); Legendre is Mathlib's `sub_one_mul_padicValNat_factorial`. Check:
  `tools/leancheck-mathlib.sh`, exit 0, no warnings; every theorem uses only propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): recomputes a(n) from Legendre's formula for n = 2..5000; equals
  Eldar's b-file ([`certificate/b096127.txt`](certificate/b096127.txt)) and a(n) = n+1 exactly at prime powers.
- Outside Lean: none. Not verified in Lean: agreement of `a` with the OEIS data terms (check.py).

**Review level.** `lean-proof`.

**Prior art** (2026-11-06). OEIS entry and history (conjecture still open there, last edit 2021); web search for the
divisibility (n^2)!/(n!)^(n+2) and digit-sum arguments; google-deepmind/formal-conjectures (FormalConjectures/OEIS)
and otoi-lab/oeis-lean-proofs: no file for A096127. No proof found. The classical fact behind step 2 is that
(n^2)!/((n!)^(n+1)) counts partitions of an n^2-set into n blocks of size n; the digit-sum argument for the
converse is ours.

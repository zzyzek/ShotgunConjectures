# OEIS A219930: odd members are 1 and 3; every member above 714 is divisible by 30

**Source.** [A219930](https://oeis.org/A219930): "n such that phi(n) represents a new lower bound for the phi
function", data 1, 3, 8, 14, 20, 36, 48, ... Three conjectures in the entry (OEIS text, checked 2026-11-08):
(1) "If n is in the sequence, then the sequence contains an infinite number of multiples of n."
(2) "Except for 1 and 3, all members of the sequence are even. If n is odd, it cannot be squarefree."
(3) "There does not exist N such that for all n > N, a(n) is divisible by 30."

**Reading.** Call n a lower bound if phi(m) >= phi(n) for every m > n. The entry's examples ("phi(8)=4, and for
n>=8, phi(n)>=4") and data are the least lower bound with each value: n is a member iff n is a lower bound and no
smaller lower bound has the same totient. This reproduces the b-file (certificate/a.c lists all 273 members
below 3.19*10^7). In (2) the sentence about odd squarefree n is read as a fallback; 3 is odd and squarefree.

**Result.**
- Conjecture (2) is true: no odd n > 3 is a lower bound, so every member other than 1 and 3 is even.
- Conjecture (3) is false: every member greater than 714 is divisible by 2, 3 and 5. The members not divisible
  by 3 are 1, 8, 14, 20, 70; those not divisible by 5 are 1, 3, 8, 14, 36, 48, 66, 96, 126, 132, 156, 252, 336, 714.
- Conjecture (1) is not settled. Members up to 3.19*10^7 contain only one multiple of 900 (900 itself) and six of 450.

**Argument.** Every step exhibits m > n with phi(m) < phi(n), so n is not a lower bound. Two estimates are used
for primes p, s and N >= 1: phi(pN) >= (p-1) phi(N), and phi(sN) <= s phi(N) (equality when s | N).

1. *Odd n.* If a prime p >= 5 divides n = pN, Bertrand gives a prime s with (p-1)/2 < s <= p-1; s is odd and
   s < p-1. Put m = 2sN. Then m > n since 2s > p, and phi(m) = phi(sN) <= s phi(N) < (p-1) phi(N) <= phi(n).
   Otherwise n = 3^k with k >= 2, and m = 4*3^(k-1) has phi(m) = 4*3^(k-2) < 6*3^(k-2) = phi(n).
2. *q not dividing n, q in {3, 5}.* For a prime p | n, p != q, and a prime s != q with p/q < s < (p-1)/(q-1), put
   m = (n/p) q s: m > n and phi(m) <= (q-1) s phi(n/p) < (p-1) phi(n/p) <= phi(n). For p >= 10^4 such s exists by
   Nagura (a prime in (x, 6x/5) for x >= 25, applied with x = p/q); certificate/moves.py lists the primes below
   10^4 without such s: {2, 5, 7, 11, 23} for q = 3 and {2, 3, 7, 11, 13, 17, 19, 23, 29, 37, 41, 43, 67} for
   q = 5. For such p, if p^(j+1) | n and a prime s != q lies in (p^j/q, p^j/(q-1)), the same move with p^j in place
   of p applies (phi(n) = p^j phi(n/p^j)); moves.py gives the exponent bounds. For q = 3 this leaves n <= 991760.
   For q = 5 and n > 3*10^7 (so 6 | n by step 1 and the q = 3 case) the 776416 remaining factorisation shapes each
   get an explicit move m = (n/d)*5*r (certificate/cert5.py, all succeed).
3. *Finite range.* certificate/a.c sieves phi to 2*10^8; every m > 2*10^8 has phi(m) > 3.27*10^7 by the
   Rosser-Schoenfeld bound phi(m) > m/(e^gamma lnln m + 2.50637/lnln m) (the exception m = 223092870 has
   phi = 36495360, also above), so all members below 3.19*10^7 are exact. Above 714 they are multiples of 30.

**Evidence.**
- Lean (Mathlib): [`A219930_mathlib.lean`](A219930_mathlib.lean), theorem `A219930_odd_not_lowerBound`: an odd
  n > 3 is not a lower bound; `A219930_members_even`. Checked with tools/leancheck-mathlib.sh, axioms propext,
  Classical.choice, Quot.sound.
- Outside Lean: step 2 (Nagura for p >= 10^4, moves.py, cert5.py in Python with sympy) and step 3 (C sieve and the
  Rosser-Schoenfeld bound).

**Review level.** Steps 1-2 re-derived by hand; step 1 Lean-checked; certificates rerun 2026-11-08.

**Prior art.** OEIS entry and b-file (no proof or counterexample noted), web search for the conjectures,
google-deepmind/formal-conjectures (no A219930 file found), checked 2026-11-08. Step 1 is the classical trick of
replacing a prime by a nearby smaller-totient factor; we found no statement of these conjectures' resolution.
Open: conjecture (1). The moves of step 2 never raise the exponent of a prime already dividing n, which is what
(1) needs for members such as 8, 36 or 900.

# OEIS A217448: a(n) exists for every n (CRT)

**Source.** OEIS [A217448](https://oeis.org/A217448): least k > 0 such that 1 + n^2 and 1 + (n+k)^2
have the same smallest prime factor. Conjecture: "a(n) exists for all n." (OEIS text,
CC BY-SA 4.0.)

**Result.** True.

**Argument.** Let q = spf(1 + n^2). Choose k by the Chinese remainder theorem with
k ≡ 0 (mod q), and for each prime ℓ < q: if ℓ = 2, n + k even (then 1 + (n+k)^2 is odd); if ℓ is
odd, n + k avoids the at most two roots of x^2 ≡ -1 (mod ℓ) (ℓ ≥ 3 leaves at least one residue).
The moduli are distinct primes, so such k > 0 exists. Then (n+k)^2 ≡ n^2 ≡ -1 (mod q), so
q | 1 + (n+k)^2, and no smaller prime divides it: spf(1 + (n+k)^2) = q. (If q = 2, n is odd and any
even k works.)

**Evidence.** Lean (Mathlib): [`A217448_mathlib.lean`](A217448_mathlib.lean), `A217448_main`: for every n >= 1 there is k > 0 with `Nat.minFac (1 + n^2) = Nat.minFac (1 + (n+k)^2)`. The Lean proof uses k = (1 + n^2)! instead of CRT: every prime l <= 1 + n^2 divides k, so l | 1 + (n+k)^2 iff l | 1 + n^2. Outside Lean: none. The b-file (n ≤ 10000) gives values for all those n (scan record).

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.

**Depends on (Mathlib).** Chinese remainder theorem over the primes below q (elementary; in Mathlib).

**Prior art.** New to OEIS, immediate (Chinese remainder theorem). [OEIS A217448](https://oeis.org/A217448) (fetched 2026-11-04) still states the conjecture; edits since 2012 do not address it. Searched: entry, OEIS cross-reference search, edit history. Worth an OEIS comment. (Prior-art review 2026-11-04.)

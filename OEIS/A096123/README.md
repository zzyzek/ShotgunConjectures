# OEIS A096123: a(n) = n!/(p-1)! for large n (p least prime with n ≤ 2p) is false

**Source.** OEIS [A096123](https://oeis.org/A096123), "Least product n*(n-1)*(n-2)*...*(n-k+1) divisible by (n-k)!", conjecture by Amarnath Murthy in the entry: a(n) = n!/(p-1)! for all sufficiently large n, where p is the least prime such that n <= 2*p. The entry adds that A096974 (the n where equality holds) indicates the conjecture is most probably false.

**Reading.** a(n) = n!/(n-k)! for the least k ≥ 0 with (n-k)! dividing n!/(n-k)!. This reproduces all 24 listed terms (`certificate/check.gp`). The entry's PARI program uses divisor (n-k+1)! instead; the argument below works for that reading too (k = p qualifies there because (p+1)!·p! divides (2p)!, as (2p)!/(p!·(p+1)!) is a Catalan number).

**Result.** False. For every prime p, a(2p) ≤ (2p)!/p! < (2p)!/(p-1)!, and p is the least prime with 2p ≤ 2p. So the conjecture fails at n = 2p for every prime p.

**Argument.** For n = 2p, k = p qualifies: (2p)!/p! is divisible by p! because p!·p! divides (2p)! (the binomial coefficient C(2p, p) is an integer). The least qualifying k is at most p, and the product n(n-1)...(n-k+1) grows with k, so a(2p) ≤ (2p)!/p!. The conjectured value is (2p)!/(p-1)! = p·(2p)!/p!, larger since p ≥ 2. Any prime q with 2p ≤ 2q has q ≥ p, so the least such prime is p.

**Evidence.**
- Lean (Mathlib): [`A096123_mathlib.lean`](A096123_mathlib.lean). `A096123_main`: for every N there is n ≥ N with a(n) ≠ n!/(q-1)! for the least prime q with n ≤ 2q; `A096123_conjecture_false` negates the conjecture as stated. `A096123` is defined as in the entry's name (least k by `Nat.find`). Outside Lean: that this definition matches the entry (data check in `certificate/check.gp`, output `certificate/check.log`).

**Review level.** `lean-proof`.

**Prior art.** Verdict `partly-known`. A096974 (Klaus Brockhaus, 2004) lists the n with equality; its terms skip every n = 2p (4, 6, 10, 14, 22, 26, ...), and its comment calls the conjecture apparently false, but neither entry gives a proof. Searched: OEIS A096123, A096974 entries, google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).

# OEIS A219197: the square root of the A199033 g.f. has no coefficient = 3 (mod 4)

**Source.** [A219197](https://oeis.org/A219197) (Hanna, 2012): a = 1, 2, 9, 46, 253, ..., the self-convolution square
root of A199033(n) = sum_k C(n+k+1, n-k) C(2n-k+1, k). G.f. formula in the entry: A = G/sqrt(1 - 2xG^2 - 3x^2G^4),
G = 1 + xG^3. Comment: "Conjecture: a(n) is never congruent to 3 modulo 4." (OEIS text checked 2026-11-06.)

**Result.** True. Moreover a(n) is odd iff n is even and n AND 2n = 0 (no two adjacent 1-bits), and then a(n) = 1
(mod 4).

**Argument.**
1. *Lagrange form.* Put t = xG^2; then G = 1/(1-t) and x = t(1-t)^2. The entry's g.f. becomes
   A = (1-t)^(-1) (1-2t-3t^2)^(-1/2), and Lagrange inversion ([x^n] H = [t^n] H(t) phi^n (1 - t phi'/phi),
   phi = (1-t)^(-2)) gives a(n) = [t^n] S(t) (1-t)^(-2n-2), S = sqrt((1-3t)/(1+t)).
2. *S mod 4.* (1-3t)/(1+t) = 1 - 4u with u = t/(1+t), so S = sqrt(1-4u) = 1 - 2 sum_{k>=1} Cat(k-1) u^k. Cat(k-1) is
   odd iff k is a power of 2, and u^(2^j) = t^(2^j)/(1+t^(2^j)) (mod 2). Hence S = 1 + 2W (mod 4) with
   W = sum_m (v2(m) + 1) t^m (mod 2), and
   a(n) = C(3n+1, n) + 2 E(n) (mod 4),  E(n) = sum_{1<=m<=n, v2(m) even} C(3n+1-m, n-m).
3. *Parity.* C(3n+1, n) = C(n + (2n+1), n) is odd iff adding n and 2n+1 has no carry, i.e. n even and n AND 2n = 0.
   By Lucas, C(3n+1-m, n-m) = C(k + (2n+1), k) with k = n-m is odd iff k AND (2n+1) = 0, so
   E(n) = #{0 <= k < n : k AND (2n+1) = 0, v2(n-k) even} (mod 2).
4. *C(3n+1, n) mod 4.* From (1+t)^(2x) = (1+t^2+2t)^x = (1+t^2)^x + 2xt(1+t^2)^(x-1) (mod 4), C(2x, 2y) = C(x, y)
   (mod 4); with C(2x+1, 2y) = C(2x, 2y)(2x+1)/(2x-2y+1) and C(2x+1, 2y+1) = C(2x, 2y)(2x+1)/(2y+1) and
   2z+1 = (-1)^z (mod 4), a carry-free C(a, b) is (-1)^N (mod 4), N = #{i : a_(i+1) = a_i = 1, b_(i+1) != b_i}. For
   a = 3n+1, b = n (n even, no adjacent 1-bits) this is N(n) = popcount(n) + #{i >= 0 : n_(i+1) = 1, (2n+1)_i = 1}.
5. *E = N (mod 2).* Write n = 2^e + n' with n' < 2^(e-1) (top bit e, next bit e2 <= e-2 if n' > 0). The k >= 2^e
   are 2^e + k'' with k'' counted by E(n'). The k < 2^e range over the span of the free positions F = {1..e-1}
   minus {e_j + 1 : j >= 2}; k = n' gives v2 = e, and for k != n', v2(n-k) = v2(n'-k) = v exactly for 2^|F cap (v, e-1]|
   values of k when v is in F (none otherwise). Mod 2 only v = max F survives, so this part is
   [max F even] + [e even]: 1 if e >= 2 and e2 != e-2 (or n' = 0), 0 if e2 = e-2 or e = 1. The same top-bit step
   changes N by 1 + [e2 = e-2] (by 1 + [e = 1] when n' = 0). Induction from E(0) = N(0) = 0 gives E = N (mod 2).
6. Hence for odd a(n): a(n) = (-1)^N + 2N = 1 (mod 4); otherwise a(n) is even. So a(n) is never 3 mod 4.

**Evidence.**
- [`certificate/f.py`](certificate/f.py): step 1 exactly (a(n) from the entry's A002426 formula equals the Lagrange
  coefficient, n <= 120) and the mod-4 formula of step 2 (n <= 120).
- [`certificate/g.py`](certificate/g.py): steps 4-5 identities (C(3n+1,n) mod 4 = (-1)^N and E = N mod 2) for all
  377 even n < 8192 without adjacent 1-bits.
- [`certificate/h.py`](certificate/h.py): A199033(n) = [t^n](1-t)^(-2n-3)(1+t)^(-1) for n <= 400 (the entry's g.f.
  formula, used in step 1).
- [`certificate/m.gp`](certificate/m.gp): a(n) mod 4 for n <= 1200 from the g.f.: residues 0, 1, 2 only
  (`m_out.txt`).
- Lean: none. Outside Lean: the whole argument; the entry's g.f. formula A = G/sqrt(1-2xG^2-3x^2G^4) (checked to
  n = 400 via h.py) is used, not re-proved.

**Review level.** `agent` (proof written here, each step checked numerically; no independent second reading).

**Prior art.** Checked 2026-11-06: entry (unannotated), not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs. No proof found.

# OEIS A228514 group: Sun's 2013 determinant congruences (nine entries)

**Source.** Conjectures of Zhi-Wei Sun (Aug 2013) in OEIS
[A228514](https://oeis.org/A228514), [A228511](https://oeis.org/A228511),
[A228304](https://oeis.org/A228304), [A228289](https://oeis.org/A228289),
[A228077](https://oeis.org/A228077), [A228005](https://oeis.org/A228005),
[A227971](https://oeis.org/A227971), [A227968](https://oeis.org/A227968),
[A227609](https://oeis.org/A227609). The scan grouped them under one title; they are nine
different claims (p an odd prime, h = (p-1)/2, (./p) the Legendre symbol).

| id | claim | status |
|---|---|---|
| A227609 | S = det[((i²+j²)/p)]_{1≤i,j≤h}: p ∤ S and (−S/p) = 1 | known: Sun, Finite Fields Appl. 56 (2019) 285–307 (arXiv:1308.2900 v9+) |
| A227968 | T = det[((i²+j²)/p)]_{0≤i,j≤h}: (2T/p) = 1 | known: same paper, (T(d,p)/p) = (2/p) for (d/p) = 1 |
| A227971 | R = det[((i+j)/p)]_{0≤i,j≤h} ≡ h! (p ≡ 1 mod 4), ≡ (2/p) (p ≡ 3 mod 4) | known: proved by Sun (Aug 2013, recorded in the entry; same paper) via det[(i+dj+c)^n] = (−d)^{n(n+1)/2}(n!)^{n+1} |
| A228005 | det[((i²+j²+1)/p)]_{1≤i,j≤h} has Legendre symbol ((2(−1)^h − 4)/p) | known: Grinberg, Sun, Zhao, arXiv:2007.06453 (Linear Multilinear Algebra), Legendre symbol of S_c(d,p) determined for p ∤ cd |
| A228304 | Hankel det[a(i+j)]_{0≤i,j<p}, a(n) = Σ(−1)^k C(n,k)^4, ≡ (−1)^h; same with c(n), ≡ 1 | known: Adamczewski, arXiv:2608.11941 (2026), OEIS Open; formal-conjectures marks it `research solved` |
| A228077 | det[((j−i)/p)]_{h×h}: unit/class-number formula | open (see below) |
| A228289 | Hankel det of Domb numbers ≡ (−1)^h(4x²−2p) mod p² | open |
| A228511 | Hankel det of Σ C(n,k)² 4^k Cat(k) ≡ (−1)^h mod p | open |
| A228514 | Hankel dets of Σ C(n,k)² C(2k,k+1) mod p², mod p | open |

**Result.** Five of the nine are theorems in the literature (cited above). The other four have
no proof found (search 2026-11-06).

**Argument (known items).** A228304 (Adamczewski): by Lucas' theorem a(p+m) ≡ 0 and
c(p+m) ≡ 0 mod p for 0 ≤ m ≤ p−2, so both Hankel matrices are anti-triangular mod p; the
determinant is (−1)^{p(p−1)/2} v^p ≡ (−1)^h v with v = a(p−1) ≡ 1, resp.
c(p−1) ≡ (−1)^h. The four Legendre-symbol items are proved in the cited papers (not
re-derived here).

**Open items, how far we got.** The anti-triangular argument does not transfer: for
A228511 and A228514, a(p+m) ≢ 0 mod p (A228514: a(p+m) ≡ 3a(m) for small m by Lucas), so
the Hankel matrix mod p has no triangular shape (`certificate/hk.py`). A228077 is the h×h
principal minor of Chapman's (h+1)×(h+1) "evil determinant" (evaluated by Vsemirnov 2012,
2013; the x-deformation by Wang–Wu–Ni, arXiv:2405.02112); the minor needs the (h,h) entry
of the inverse, which those decompositions do not give directly. For A228289 only the
related sums Σ D_n/4^n, Σ D_n/16^n mod p² are proved (Z.-H. Sun; Mao–Liu).

**Evidence.** `certificate/leg.py` re-checks the four Legendre-symbol claims for all primes
3 ≤ p < 260 (determinants mod p); no failures. No Lean: the cited proofs need determinant
evaluations and Gauss-sum or Lucas arguments over all p; an OEIS Open Lean proof of A228304
exists (Adamczewski 2026).

**Review level.** `agent` for the citations; `rechecked` numerically (p < 260).

**Prior art.** Checked 2026-11-06: OEIS entries; arXiv 1308.2900 (abstract, versions),
2007.06453, 2405.02112, 2405.03626, 2409.08213, 2507.18589, 2608.11941; web search;
google-deepmind/formal-conjectures (only A228304, `research solved`);
otoi-lab/oeis-lean-proofs (none).

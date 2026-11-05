# OEIS A024187: e_n(3, 4, ..., n+3) is A001711

**Source.** OEIS [A024187](https://oeis.org/A024187) (n-th elementary symmetric function of 3, 4, ..., n+3,
offset 1), comment by R. Stephan (Dec 30 2004): "Conjecture: essentially the same as A001711."

**Reading.** A001711 (offset 0) is "Generalized Stirling numbers, [n+4,4]_3". The entry reads this (P. Hadjicostas,
2020) as a(n) = R_{n+1}^1(−3,−1) = [x^1] Π_{r=0..n}(x+3+r) (Mitrinović numbers); this agrees with Broder's
r-Stirling numbers, Σ_k [m,k]_r x^k = x^r (x+r)(x+r+1)···(x+m−1) at m = n+4, r = 3, k = 4. "Essentially the same"
is read as A024187(n) = A001711(n) for n ≥ 1 (A001711 has the extra term a(0) = 1).

**Result.** True: A024187(n) = A001711(n) for every n ≥ 1 (and the formulas also agree at n = 0).

**Argument.** Vieta: the coefficient of x^1 in Π_{c∈S}(x+c) for |S| = n+1 is e_n(S); here S = {3, ..., n+3}.

**Evidence.**
- Lean (Mathlib): [`A024187_mathlib.lean`](A024187_mathlib.lean). `A024187_conjecture (n : ℕ) : A024187 n = A001711 n`
  (Mathlib's `Finset.prod_X_add_C_coeff`). Supporting: `A001711_rec` (a(n+1) = (n+4)a(n) + 3·4···(n+3)),
  `A001711_data` (a(0..10) against the entry). Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: e_n by enumeration vs the entry's terms; [x]Π vs (n+3)!/2·Σ 1/(3+s).
- Outside Lean: the reading of "[n+4,4]_3" above.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: the A001711 entry itself gives a(n) = [x]Π_{r=0..n}(x+3+r) =
(Π(3+r))·Σ 1/(3+s) (Hadjicostas, Jun 2020), and W. Lang's table A196845 (2011) of e_k(3, ..., n+2) lists A001711
as its first subdiagonal; with Vieta's formula the conjecture is immediate. Web search; not in
google-deepmind/formal-conjectures.

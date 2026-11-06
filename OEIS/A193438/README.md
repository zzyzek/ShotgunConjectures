# OEIS A193437 / A193438: p^floor(n/p) divides a(n) for primes p = 1 (mod 3), resp. p = 1 (mod 4)

**Source.** [A193437](https://oeis.org/A193437): e.g.f. exp(Sum_{n>=0} x^(3n+1)/(3n+1)), the number of permutations of
n elements with every cycle length = 1 (mod 3). [A193438](https://oeis.org/A193438): the same with 4 in place of 3.
Conjectures (Paul D. Hanna, in the entries): a(n) is divisible by p^floor(n/p) for every prime p = 1 (mod 3),
respectively p = 1 (mod 4). (OEIS text, checked 2026-11-06; both entries now link Kallat's paper.)

**Result.** True, and stronger: v_p(a(n)) >= v_p(n!) >= floor(n/p). Known: A. Kallat, "A p-adic valuation calculus
for permutations with restricted cycle lengths", arXiv:2610.40342 (Oct 29 2026), Theorem 8.15 and Remark 8.16, with a
Lean 4 + Mathlib proof in its ancillary files (`anc/lean/lean-restricted/CongruenceRestricted/Saturation.lean`:
`saturated_valuation`, `sat_residue`).

**Argument** (re-derived independently). Let L be the allowed cycle lengths, r = 3 or 4, p = 1 (mod r). Then
pl = l (mod r), so l is in L iff pl is in L. Write each l in L as u p^k with p not dividing u; u is in L. Then
Sum_{l in L} x^l / l = Sum_{u in L, p ∤ u} (1/u) Sum_k (x^u)^(p^k) / p^k, so the e.g.f. is
A(x) = Prod_{u} E_p(x^u)^(1/u), with E_p(y) = exp(Sum_k y^(p^k)/p^k) the Artin–Hasse exponential. E_p has
p-integral coefficients (Dwork's lemma) and 1/u is a p-adic integer, so each factor and the x-adically convergent
product lie in Z_(p)[[x]]. Hence a(n)/n! is p-integral. This is the Dieudonné–Dwork criterion for sets closed under
multiplication and division by p, as in Kallat's Theorem 8.15.

**Evidence.**
- Kallat's Lean files (external, not re-run here): `saturated_valuation` (v_p(a_A(n)) >= v_p(n!) for p-saturated A)
  and `sat_residue` (a residue class mod M is p-saturated when p = 1 mod M); Kallat states axioms propext,
  Classical.choice, Quot.sound, no sorry, no native_decide (Lean 4.31.0).
- [`certificate/check.py`](certificate/check.py): the data terms, and v_p(a(n)) >= v_p(n!) >= floor(n/p) for all
  primes p < 60 in the class, n <= 400, both sequences.
- Outside Lean (in this repository): everything; the Lean proof is Kallat's and was not checked here.

**Review level.** `rechecked` (independent derivation via the Artin–Hasse product, numerical check).

**Prior art.** Checked 2026-11-06: OEIS A193437 and A193438 histories (Kallat's arXiv:2610.40342 and arXiv:2610.15849
added Oct-Nov 2026); arXiv:2610.40342 text and ancillary Lean files; google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs (no entries). Verdict: known.

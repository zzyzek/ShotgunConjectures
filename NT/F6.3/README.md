# Guy UPINT F6 / Erdős #436: three consecutive fifth-power residues — partial results

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section F6, and
[Erdős problem #436](https://www.erdosproblems.com/436) (paraphrased): r(k,3,p) is the least r ≥ 1 such that
r, r+1, r+2 are all nonzero k-th power residues mod p, and Λ(k,3) = limsup_p r(k,3,p). Lehmer, Lehmer, Mills and
Selfridge proved Λ(3,3) = 23532; the Lehmers proved Λ(k,3) = ∞ for even k. Is Λ(k,3) finite for odd k ≥ 5?
(Smallest open case k = 5; open per erdosproblems.com, last update 2025-08-31.)

**Reading.** For p ≢ 1 (mod 5) every nonzero residue is a fifth power and r = 1, so only p ≡ 1 (mod 5) matter.

**Result.** Partial; the question stays open.
1. (Reduction, classical ingredients.) Λ(5,3) = sup over completely additive f : ℕ⁺ → ℤ/5 of the least r with
   f(r) = f(r+1) = f(r+2) = 0, and Λ(5,3) < ∞ iff every such f has at least one zero triple.
2. (Lean, new as a stated obstruction.) For every odd k, no completely additive f : ℕ⁺ → ℤ/k of character type
   (f(n) depends only on n mod Q for n prime to Q, any values on primes dividing Q) avoids zero triples:
   r = Q^k − 1 works. So an f proving Λ(k,3) = ∞ for odd k cannot be of the Lehmer (character) type used for
   even k; it has to be aperiodic on units.
3. (Computation, new.) Λ(5,3) ≥ 399 999: an explicit f with no zero triple r ≤ 399 998 (SAT, CaDiCaL), checked
   from scratch from its values at primes. The same encoding reproduces Λ(3,3) = 23532 exactly
   (satisfiable at N = 23533, unsatisfiable at N = 23534).

**Argument.** (1) Let p ≡ 1 (mod 5) and χ_p a character of order 5; n is a nonzero fifth-power residue iff
χ_p(n) = 1, so f_p = log χ_p is completely additive with values in ℤ/5 on n < p. Conversely, for primes
q_1 < … < q_s and any target values, Kummer theory gives Gal(Q(ζ_5, q_1^{1/5}, …, q_s^{1/5})/Q(ζ_5)) ≅ (ℤ/5)^s,
and Chebotarev gives infinitely many p with χ_p(q_i) the prescribed fifth roots of unity (up to the choice of
χ_p, which does not change the zero set). Hence an f avoiding zero triples up to N gives infinitely many p with
r(5,3,p) > N − 2, and conversely. Compactness (König's lemma over the finitely many choices at each prime)
turns "every f has a zero triple" into a uniform bound. (2) With f of character type: f(Q^k) = k·f(Q) = 0;
Q^k + 1 ≡ 1 (mod Q) so f(Q^k + 1) = f(1) = 0; Q^k − 1 ≡ Q − 1 (mod Q) and (Q − 1)² ≡ 1, so
2 f(Q − 1) = 0 in ℤ/k, and k odd gives f(Q − 1) = 0. (3) The CNF has one-hot variables for f(n), n ≤ N,
the clauses f(p m) = f(p) + f(m) for the least prime factor p, the triple clauses, and f(2) ∈ {0, 1} (scaling by
a unit of ℤ/5 preserves zero sets).

**Evidence.**
- Lean (core): [`F6_3.lean`](F6_3.lean), `unit_periodic_has_triple` (values read mod k; "prime to Q" expressed as
  invertible mod Q). `tools/leancheck.sh`: OK, no warnings, axioms propext, Classical.choice, Quot.sound.
- [`certificate/gen.py`](certificate/gen.py) (CNF), [`certificate/verify_witness.py`](certificate/verify_witness.py)
  (decodes a model and re-checks it from the prime values), [`certificate/check_witness.py`](certificate/check_witness.py) (re-checks the stored witness: prints `primes 33860 zero triples 0`), [`certificate/witness_k5_N400000.txt.gz`](certificate/witness_k5_N400000.txt.gz)
  (f(p) for the 33 860 primes p ≤ 400 000; 141 409 zeros of f in [1, 400 000], no zero triple). CaDiCaL run: 11 s, 1.7 GB.
- Outside Lean: the reduction (1) (Chebotarev, Kummer theory, compactness), the witness check (Python), and the
  k = 3 calibration.

**Review level.** `lean-proof` for (2); `rechecked` for (3).

**Prior art.** Checked 2026-11-07: erdosproblems.com #436 (open), teorth/erdosproblems data (open, 2025-08-31),
google-deepmind/formal-conjectures `ErdosProblems/436.lean` (part ii `research open`; no proofs), Guy F6.
No published lower bound for Λ(5,3) was found. Remark (1) is standard (it is how the Lehmers and Hildebrand work).

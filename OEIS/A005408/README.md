# OEIS A005408: one-coach primes and the first q odd numbers

**Source.** [A005408](https://oeis.org/A005408), comment by G. W. Adamson (2012): "Conjecture on primes with
one coach (A216371) relating to the odd integers: iff an integer is in A216371 (primes with one coach either
of the form 4q-1 or 4q+1, (q > 0)); the top row of its coach is composed of a permutation of the first q odd
integers." (OEIS text, CC BY-SA 4.0.)

**Reading.** The coach of an odd b (Hilton–Pedersen) has top row a_0 = 1, a_{i+1} = odd part of b − a_i,
until it returns to 1. The claim: b = 4q ± 1 is in A216371 (prime with one coach) iff the top row of the
coach of 1 is a permutation of 1, 3, …, 2q − 1.

**Result.** True; a definitional identity.

**Argument.** The map a ↦ odd part of (b − a) sends odd numbers below b/2 to odd numbers below b/2, keeps
coprimality to b, and is injective (b − a lies in (b/2, b), which holds at most one number c·2^j for a given
odd c). So it permutes the odd residues below b/2 that are coprime to b, and the coaches are its cycles.
There are exactly q odd numbers below b/2. If b is prime all of them are coprime to b, so one coach means
the coach of 1 runs through all q. Conversely, if the coach of 1 runs through all q odd numbers below b/2,
each is coprime to b; a composite odd b has an odd prime factor ≤ √b < b/2, so b is prime, and it has
one coach.

**Evidence.**
- Lean (Mathlib): [`A005408_mathlib.lean`](A005408_mathlib.lean) proves `step_bijOn` (for odd b, a ↦ oddPart(b − a) is a bijection of D(b) = {a odd, 2a < b, gcd(a, b) = 1}, so the coaches are its cycles) and `A005408_main`: for odd b = 4q ± 1, q > 0, (b prime ∧ D(b) ⊆ coach of 1) ↔ the coach of 1 (set of top-row entries) = {a odd, a < 2q}. Outside Lean: nothing beyond the reading stated in the file header (top row as the set of its entries, "one coach" as D(b) ⊆ coach of 1).
- `certificate/check.py`: both sides agree for every odd b < 2·10^4.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`A005408_mathlib.lean`](A005408_mathlib.lean)) under the reading stated in its header.
**Prior art.** Partly known. For prime b the claim follows from the Hilton-Pedersen Coach theorem phi(b) = 2ck as quoted in [A216371](https://oeis.org/A216371) (one coach iff k = (b-1)/2 = q) and counting the q odd numbers below b/2; the converse (a composite b never qualifies) is not stated there. The same conjecture is open in both [A005408](https://oeis.org/A005408) and [A216371](https://oeis.org/A216371). Searched OEIS entries, references and history, web. Checked 2026-11-04.

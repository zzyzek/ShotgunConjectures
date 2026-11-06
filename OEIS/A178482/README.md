# OEIS A178482: Kimberling's change-of-base conjecture for phi-antipalindromic numbers (known)

**Source.** [A178482](https://oeis.org/A178482) (V. Shevelev, 2010), phi-antipalindromic numbers. "Conjecture: this is
the sequence of numbers k for which f(k) is an integer, where f(x) is the change-of-base function defined at
A214969 using b=phi and c=b^2." (C. Kimberling, Oct 17 2012; OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True (known). The entry now says (J. Shallit, Aug 28 2025) that the conjecture "has been proven by
Ingrid Vukusic and myself", with the alternate characterisation: the positive integers whose base-phi
expansion uses only even exponents of phi.

**Argument.** Not reproduced. The proof is in J. Shallit and I. Vukusic, "New properties of the
φ-representation of integers", arXiv:2509.16150 (2025, rev. 2026): automata for base-phi representations,
checked with the Walnut prover. The entry also records a 21-state automaton for the Zeckendorf
representations of the members.

**Evidence.** Citation only. Lean: none (a Lean proof would need base-phi representations and the
automaton argument formalised; not attempted within the 1 h cap). Outside Lean: everything.

**Review level.** `agent` (not re-derived).

**Prior art.** Shallit-Vukusic, arXiv:2509.16150 (checked 2026-11-06 by abstract/search excerpt). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones).

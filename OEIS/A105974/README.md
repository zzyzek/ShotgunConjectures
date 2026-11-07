# OEIS A105974: (A001035(n) - 1)/2 modulo m

**Source.** [A105974](https://oeis.org/A105974), (A001035(n) - 1)/2, A001035 = number of labeled posets on n points.
Comment: "Conjectures: a(n) is (pre)periodic modulo m for all m, the lengths of the ending periods being given by
2*A000010(m) if m is a power of 2 and A000010(m) otherwise." (OEIS text, CC BY-SA 4.0, entry as of May 26 2017,
checked 2026-11-07.)

**Result.** Partial. The periodicity part is true (known); the period lengths remain open.

**Argument (periodicity).** Specker-Blatter theorem: for a class of finite structures over binary relations
definable in monadic second-order logic, the number of labeled structures on [n] satisfies, for every modulus M, a
linear recurrence with constant coefficients mod M, hence is ultimately periodic mod M. Posets are first-order
definable with one binary relation, so A001035 is ultimately periodic mod 2m, and a(n) = (A001035(n) - 1)/2 is
ultimately periodic mod m.

**Not settled.** The period lengths 2 phi(m) / phi(m). For m = p prime this would follow from the congruence
A001035(n+p) = A001035(n+1) mod p noted (unproved) by A. Alkan in A001035; we did not find a proof.

**Evidence.** Lean: none. Outside Lean: Specker-Blatter.

**Review level.** `agent` (citation applied, not re-derived).

**Prior art.** C. Blatter and E. Specker, Le nombre de structures finies d'une th\'eorie \`a caract\`ere fini,
Sciences Math\'ematiques, Fonds National de la Recherche Scientifique, Bruxelles (1981) 41-44; E. Specker,
Application of logic and combinatorics to enumeration problems, in Trends in Theoretical Computer Science (1988);
E. Fischer and J. A. Makowsky, The Specker-Blatter theorem revisited, COCOON 2003, LNCS 2697. Searched 2026-11-07:
web, A001035 entry, arXiv:2606.31526 (uses the periodicity as a check, no proof of period lengths);
not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

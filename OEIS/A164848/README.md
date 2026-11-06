# OEIS A164848: a(n) = A026741(n)/A051712(n+1) has period 24

**Source.** OEIS [A164848](https://oeis.org/A164848) (Paul Curtz, 2009), a(n) = A026741(n)/A051712(n+1):
"Conjecture (checked for the first 3000 entries): periodic with a(n+24)=a(n)." (OEIS text, CC BY-SA 4.0.)

**Reading.** A026741(n) = n for odd n, n/2 for even n. A051712(n) is the numerator of
b(n) - b(n+1) with b(n) = n/((n+1)(n+2)) (offset 1). Offset of A164848 is 1; a(1..105) agree with the data.

**Result.** True: a(n) = gcd(n, 24) for odd n and gcd(n, 24)/2 for even n, so a(n+24) = a(n) for all n >= 1.
This also gives Howroyd's formula a(n) = gcd(12, n/gcd(2, n)) listed in the entry.

**Argument.** b(n+1) - b(n+2) = n(n+3)/((n+2)(n+3)^2(n+4)). Since (n+2)(n+3)(n+4) = 24 + n(n^2 + 9n + 26),
gcd(n(n+3), (n+2)(n+3)^2(n+4)) = (n+3)·gcd(n, 24), so A051712(n+1) = n/g with g = gcd(n, 24). Then
a(n) = n/(n/g) = g for odd n and (n/2)/(n/g) = g/2 for even n (g is even). Both depend only on n mod 24.

**Evidence.**
- Lean (core): [`A164848.lean`](A164848.lean): `A051712_succ`, `A164848_closed`, `A164848_periodic`
  (the conjecture, for every n >= 1), `A164848_terms` (a(1..48) equal the listed terms). The numerator is
  computed with core `Rat` (`Rat.divInt`, `Rat.num`). Axioms propext, Classical.choice, Quot.sound.
  Outside Lean: none for the conjecture under the reading above; `certificate/check.gp` re-checks the data,
  the period and Howroyd's formula for n <= 10^5 from the rational definition.

**Review level.** `lean-proof`.

**Prior art.** Known: the entry carries Andrew Howroyd's formula a(n) = gcd(12, n/gcd(2, n)) (Jul 2018,
stated without proof) and Amiram Eldar's multiplicative description (Oct 2023), each of which implies the
period 24; the conjecture comment was not edited. No Lean proof found (google-deepmind/formal-conjectures
has no OEIS/164848.lean; otoi-lab/oeis-lean-proofs has no entry). Searched OEIS entry and history,
A051712, A026741, web. Checked 2026-11-06.

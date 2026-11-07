# OEIS A071561: almost all integers have no middle divisor, so a(n)/n -> 1, not 4/3

**Source.** [A071561](https://oeis.org/A071561): numbers with no middle divisors (divisors d with
sqrt(k/2) <= d < sqrt(2k)). "Conjecture: lim_{n->oo} a(n)/n = 4/3." Amiram Eldar (Jul 27 2024): "numerical
calculations suggest that this limit is smaller than 4/3. See A071540." The 2013 wiki list states it as the
density of numbers with no middle divisor tending to 3/4. (OEIS text, CC BY-SA 4.0, cached entry read 2026-11-07.)

**Result.** False: the numbers with a middle divisor (A071562) have density 0, so A071561 has density 1 and
a(n)/n -> 1.

**Argument.** If k in (X/2, X] has a middle divisor d, then sqrt(X)/2 <= d < sqrt(2X), so k has a divisor in one
of the three intervals (y, 2y], (2y, 4y], (4y, 8y] with y = sqrt(X)/4 (rounding the endpoints by a factor 2 at
most). By Ford (Ann. of Math. 168 (2008), Theorem 1, with the symmetry d <-> k/d for the range above sqrt(X)),
H(X, z, 2z) = #{k <= X : k has a divisor in (z, 2z]} << X (log z)^(-delta) (log log z)^(-3/2) for
3 <= z <= X/4, delta = 1 - (1 + log log 2)/log 2 = 0.086. Hence the count of k in (X/2, X] with a middle divisor
is << X/(log X)^delta. Summing over X = x/2^j with X >= sqrt(x) gives << x/(log x)^delta, and k < sqrt(x) adds at
most sqrt(x). So #{k <= x : k has a middle divisor} = o(x). (The weaker statement H(x, y, 2y) = o(x) as y -> oo,
Erdős 1960 / Tenenbaum 1984, already suffices with a uniformity check; Ford's bound makes it explicit.)

**Evidence.** [`certificate/check.py`](certificate/check.py): the proportion of k <= 10^n with a middle divisor
(A071541(n)/10^n; recomputed for n <= 6, read from A071540 for n = 7..10) falls 0.60, 0.43, ..., 0.218 and tracks
Ford's shape (log y)^(-delta)(log log y)^(-3/2), y = 10^(n/2): 0.25 vs 0.25 at n = 8, 0.218 vs 0.212 at n = 10.
Lean: none. Outside Lean: Ford's theorem (2008, Theorem 1).

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07. The entry and A071562, A071540, A071541, A067742 state no density result
(A071562 links Maier-Tenenbaum 1984, which concerns a different question). Ford's theorem is the standard result
on the multiplication-table problem; we found no place where it is applied to this conjecture. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).

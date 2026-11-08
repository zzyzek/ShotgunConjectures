# OEIS A228762: Sun's circular permutations with distinct differences (R-sequenceability)

**Source.** [A228762](https://oeis.org/A228762), Zhi-Wei Sun, Sep 03 2013; Z.-W. Sun, *Some new problems in
additive combinatorics*, arXiv:1309.1679. Conjecture: a(n) > 0 for odd n > 1; in general every additive abelian
group G of odd order n > 1 has a cyclic ordering a_1, ..., a_{n-1} of its nonzero elements with a_1 - a_2, ...,
a_{n-1} - a_1 pairwise distinct. (OEIS text, CC BY-SA 4.0, cached entry read 2026-11-08.)

**Result.** True, known. The property is exactly R-sequenceability (Ringel 1974; Friedlander, Gordon and Miller
1978): the non-identity elements of G can be arranged cyclically so that the quotients of successive pairs are
distinct. Friedlander, Gordon and Miller conjectured that every abelian group whose Sylow 2-subgroup is trivial
or non-cyclic is R-sequenceable; B. Alspach, D. L. Kreher and A. Pastine, "The Friedlander-Gordon-Miller
conjecture is true", Australas. J. Combin. 67(1) (2017) 11-24, completed the proof. An abelian group of odd order
has trivial Sylow 2-subgroup, so Sun's general conjecture, and a(n) > 0 for odd n > 1, follow.

**Argument.** Citation above. The entry's own primitive-root construction covers prime n.

**Evidence.**
- Core Lean: [`A228762.lean`](A228762.lean): witnesses for Z_9, Z_15, Z_21 (from the entry) and Z_3 x Z_3,
  Z_3 x Z_9, Z_5 x Z_5 (from `certificate/search.py`), each checked by kernel evaluation; no axioms.
- Outside Lean: the theorem of Alspach, Kreher and Pastine (cited, not formalised).

**Review level.** lean-witness for the small cases; citation for the general statement.

**Prior art.** Checked 2026-11-08: Australas. J. Combin. 67 p. 11 abstract (ajc-new.maths.uq.edu.au/v67.p011),
OEIS entry, google-deepmind/formal-conjectures (no OEIS/228762 file), otoi-lab/oeis-lean-proofs (no file).
Open strengthening: the entry's counts a(n) (growth rate of the number of R-sequencings of Z_n) have no proved
asymptotic.

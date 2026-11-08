# OEIS A212920: Coman's conjectures on Carmichael numbers in progressions through 1729

**Source.** [A212920](https://oeis.org/A212920) (Carmichael numbers divisible by 1729), Marius Coman, May 31 2012.
The comments state four conjectures, paraphrased: (1) if m*126 + n = 1729 with m*126 > n, there are infinitely many
Carmichael numbers C with C mod m*126 = n (the entry's text has "m*234" as the modulus here, but its examples, e.g.
C mod 882 = 847 for m = 7, use m*126); (2) the same with 234; (3) the same with 342; (4) for a Carmichael number
C1 with prime factor d and m*18*d + n = C1, infinitely many Carmichael C with C mod m*18*d = n.

**Reading.** Modulus m*126 in (1), as in the entry's examples. In (4) the entry has n > m*18*d, so "C mod m*18*d
= n" is read as the congruence C = n (mod m*18*d).

**Result.** All four hold, conditional only on a published-as-preprint theorem: each progression contains a
Carmichael number (1729 = m*126 + n, resp. C1), and D. Larsen, *Carmichael numbers in all possible arithmetic
progressions*, arXiv:2504.09056 (2025), proves that every arithmetic progression contains either no Carmichael
number or infinitely many. The stronger form with 1729 | C also holds (apply the dichotomy to 1729 mod
lcm(m*126, 1729)). If the literal modulus m*234 is kept in (1), the progression n mod 234m need not contain 1729 and
the claim reduces to Larsen's compatibility criterion case by case; not treated.

**Evidence.**
- Lean (Mathlib + library): [`A212920_mathlib.lean`](A212920_mathlib.lean). `LarsenDichotomy` states Larsen's
  theorem as a Prop; `A212920_conj1` .. `_conj4` and `A212920_conj1_div1729` derive the conjectures from it;
  `carmichael_1729` (Korselt, `isCarmichael_of_factors`). Axioms propext, Classical.choice, Quot.sound.
- Outside Lean: Larsen's theorem (hypothesis `LarsenDichotomy`; arXiv preprint, no journal reference found
  2026-11-08).

**Review level.** lean-proof of the reduction; citation for Larsen.

**Prior art.** Checked 2026-11-08: OEIS entry, arXiv:2504.09056 abstract, Wright (2013) for the coprime case,
google-deepmind/formal-conjectures (no OEIS/212920 file). The entry does not cite Larsen. Open strengthening: a
count of Carmichael numbers <= x in such a progression (Larsen gives infinitude, a lower bound of the shape x^c for
coprime progressions is due to Wright and others; the non-coprime count is not stated).

# OEIS A078008: even denominators in the rows of the Farey tree

**Source.** [A078008](https://oeis.org/A078008), expansion of (1-x)/((1+x)(1-2x)) = 1, 0, 2, 2, 6, 10, 22, ...
Comment (Adamson, 2003): "Conjecture: a(n) = the number of fractions in the infinite Farey row of 2^n terms with
even denominators. Compare the Salamin & Gosper item in the Beeler et al. link" (HAKMEM item 54: a random
rational has even denominator with probability 1/3). (OEIS text checked 2026-11-06.)

**Reading.** The "infinite Farey row of 2^n terms" is row n of the Stern-Brocot (Farey) tree of (0,1): row 0 is
{1/2}, row 1 is {1/3, 2/3}, row 2 is {1/4, 2/5, 3/5, 3/4}; each fraction is the mediant of its two Farey neighbours
and row n holds the 2^n fractions inserted at step n+1 of the mediant construction. This reading reproduces
1, 0, 2, 2. (In the full Stern-Brocot tree of (0, infinity), rooted at 1/1, the count is A001045(n) instead;
A078008(n) there counts fractions with odd numerator and odd denominator.)

**Result.** True: for every n >= 0 row n has exactly a(n) = (2^n + 2(-1)^n)/3 fractions with even denominator.

**Argument.** Store a node as its neighbours a/b < c/d (fraction (a+c)/(b+d)); then bc - ad = 1, preserved by the
children (a/b, (a+c)/(b+d)) and ((a+c)/(b+d), c/d). So b, d are not both even. The children have denominators
2b+d = d and b+2d = b (mod 2), so the number of even-denominator children is [b even] + [d even] = 1 - [b+d even].
Summing over row n: E(n+1) = 2^n - E(n), E(0) = 1. The recurrence a(n+2) = a(n+1) + 2a(n), a(0) = 1, a(1) = 0
gives a(n+1) + a(n) = 2^n, so E(n) = a(n).

**Evidence.**
- Lean (Mathlib): [`A078008_mathlib.lean`](A078008_mathlib.lean). `row n` built by mediants from (0,1,1,1);
  `evenDen n` counts nodes with b + d even. Main theorem `A078008_farey : evenDen n = A078008 n`, with `A078008`
  the recurrence of the g.f. Lemmas `inv_row` (bc = ad + 1), `node_count`, `step`, `row_facts` (length 2^n and
  E(n+1) + E(n) = 2^n), `A078008_add`. Check `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext,
  Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): rows n <= 15 as fractions; counts equal (2^n + 2(-1)^n)/3.
- Outside Lean: the g.f. (1-x)/((1+x)(1-2x)) gives the recurrence (coefficient comparison); the reading.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry (comment unannotated), HAKMEM item 54 (states the 1/3 density only).
The parity-class transfer on the Stern-Brocot tree is folklore (it is the reason for the 1/3 in item 54); no
written proof of this exact count found. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

# OEIS A214444 vs A214451: block boundaries never coincide (partial)

**Source.** [A214444](https://oeis.org/A214444): "Arithmetic mean of next a(n) successive squares is prime", blocks
starting at 0^2; [A214451](https://oeis.org/A214451): the same starting at 1^2. Conjecture in A214444: "for some k
and x, a(n)=A214451(n+x) for n>k." (OEIS text, checked 2026-11-07.)

**Result.** Partial. Every block start of A214444 is ≡ 0 or 3 (mod 4) and every block start of A214451 is ≡ 1 or 2
(mod 4), so the two partitions never share a boundary; the greedy chains never merge. The conjecture is still open:
eventual agreement of the lengths would need the two partitions to be translates by a fixed offset D ≡ 2 (mod 4)
from some point on.

**Argument.** The mean of s^2, ..., (s+l)^2 is M with 6M = 6s^2 + 6sl + l(2l+1). A prime mean is odd (M = 2 has
no solution), so 6M ≡ 2 (mod 4); this forces l even, and the table mod 4 gives: s ≡ 0 → next start s + l + 1 ≡ 3,
s ≡ 3 → 0, s ≡ 1 → 2, s ≡ 2 → 1. Start 0 stays in {0, 3}, start 1 stays in {1, 2}.

**Evidence.** [`A214444_mathlib.lean`](A214444_mathlib.lean): `block_class` (any block with prime mean, not only the
shortest), main theorem `A214444_A214451_starts_disjoint` about the greedy starts as defined in the entries.
Axioms: propext, Classical.choice, Quot.sound. Outside Lean: nothing for the partial claim.
Numerics (outside Lean): `certificate/merge_search.py` follows both chains for 200 000 blocks (starts up to
1.9 * 10^7) with no common start, as the theorem says; `certificate/common_runs.py`: over the first 20 000 blocks
the longest run with a(n+i) = A214451(n+x+i) has length 6, so the data give no support for the conjecture.

**Review level.** lean-proof (partial claim).

**Prior art.** OEIS A214444, A214451 entries (A214451: R. Israel asks whether every A007310 term occurs); web search;
google-deepmind/formal-conjectures (HEAD 2026-11-06), otoi-lab/oeis-lean-proofs: nothing. Checked 2026-11-07.

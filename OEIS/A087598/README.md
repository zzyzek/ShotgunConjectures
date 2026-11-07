# OEIS A087598: the sequence is finite (Alekseyev 2024), so "infinite" is false

**Source.** OEIS [A087598](https://oeis.org/A087598): numbers m such that m, A040115(m),
A040115(A040115(m)), …, 0 are all triangular (A040115: absolute differences of adjacent digits).
Old comment (2003): "Conjecture: Sequence is infinite." Replaced on 2024-08-02 by Max Alekseyev:
a 21st term would need A040115(term) among the listed terms; A040115(x) = t reduces to integral
points on finitely many elliptic curves; computation shows no new number, "Hence the sequence is
finite and complete" (keywords fini, full). Data: 20 terms, largest 333336.

**Result.** False (known): the sequence has exactly 20 terms.

**Evidence.** Citation only (literature-likely item; the elliptic-curve integral-point computation
is outside reach of Lean here). `lean_status: none`. Outside Lean: Alekseyev's reduction and
integral-point computation.

**Review level.** `agent` (not re-derived).

**Prior art.** M. Alekseyev, A087598 comment, 2024-08-02 (OEIS history checked 2026-11-07). Not in
formal-conjectures or oeis-lean-proofs.

# OEIS A160217: every greedy start m merges with A160217

**Source.** [A160217](https://oeis.org/A160217) (Vladimir Shevelev, May 04 2009): "Minimal increasing sequence with
a(1)=3 and the property that a(n) and n are both in or both not in A003159." Comment: "Conjecture: Let m>3 belong
to A003159. Define the sequence b(n) to be the minimal increasing sequence with b(1)=m and the property that b(n)
and n are both in or both not in A003159. Then a(n)=b(n) for all n larger than some m-dependent minimum index."
(OEIS text, CC BY-SA 4.0, revision #15 of Dec 15 2018, checked 2026-11-06.) A003159: n whose 2-adic valuation is
even.

**Result.** True.

**Argument.** Write χ(x) = 1 if v₂(x) is even. b(n+1) is the least y > b(n) with χ(y) = χ(n+1).
1. a(n) = 2n+1 if χ(n) = 1, a(n) = 2n+2 otherwise (the formula in the entry); so a advances by 2 at χ(n)=χ(n+1)=1,
   by 3 at χ(n)=1, χ(n+1)=0, by 1 at χ(n)=0.
2. From any x with χ(x) = 1 the next member is within 2 and the next non-member within 3 (an odd number or a
   number ≡ 2 mod 4 is close by); from χ(x) = 0 (x even) the next member is x+1. Since χ(b(n)) = χ(n), b advances
   at most as much as a, so d(n) = b(n) − a(n) never increases; d ≥ 0 because the greedy step is monotone in its
   start. Hence d is eventually a constant D.
3. D odd: at an odd n, b(n) = 2n+1+D is even, so b advances by at most 1 (next step member) or 2 (b ≡ 0 mod 4,
   next step non-member), less than a. Contradiction.
4. D = 2e > 0: pick t large with χ(t) = 1 and χ(t+e) = 0 (if e = 2^f g, g odd: t = 2^f(4N+g) for f even,
   t = 2^(f+1)(2N+1) for f odd). Then z = 2(t+e) is a member, b(t) = 2t+1+2e = z+1, and b(t−1) ≤ 2t+2e = z.
   If b(t−1) < z the greedy step to b(t) would stop at z; if b(t−1) = z then χ(t−1) = 0 but χ(z) = 1. Contradiction.
So D = 0.

**Evidence.**
- Lean (Mathlib): [`A160217_mathlib.lean`](A160217_mathlib.lean). `A160217_conjecture`: for m > 3 with chi m,
  ∃ N, ∀ n ≥ N, gseq m n = gseq 3 n, where gseq m is the greedy sequence from m defined by the OEIS rule
  (`nxt x c` = least y > x with chi y = c, via Nat.find). Also `A160217_formula`. Axioms propext,
  Classical.choice, Quot.sound; no sorry, no native_decide, no warnings; checked with `tools/leancheck-mathlib.sh`.
- [`certificate/check.py`](certificate/check.py): for all members 3 < m < 3000 the gap never increases and merging
  happens by n ≈ 1.4 m.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry still states the conjecture. Shevelev, arXiv:0904.2101 (2009), proves
merging for the finer equivalence "same v₂" (Theorem 2) and for Thue–Morse parity (Theorem 3), not for the parity
of v₂ used here. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06).

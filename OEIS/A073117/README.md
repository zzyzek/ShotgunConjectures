# OEIS A073117: Cloitre's eventual-increment conjecture (partial: listed values confirmed)

**Source.** [A073117](https://oeis.org/A073117), a(n+1) = a(n) + (a(n) mod n), a(1) = 1. Comment by B. Cloitre
(Aug 20 2002): for integers a and b(1), if b(n+1) = b(n) + (b(n) mod (n+a)), there is an integer x(a, b(1)) with
b(n+1) = b(n) + x(a, b(1)) for all large n; listed: x(0,1) = x(1,1) = x(2,1) = 97, x(3,1) = 1, x(4,1) = 3,
x(5,1) = 3, x(6,1) = 6, x(97,1) = 43, x(0,11) = 2. (OEIS text, CC BY-SA 4.0, rev #20, read 2026-11-06.)
The same dynamics is A094405/A066910 (partial sums S of A094405 satisfy S(n) = S(n-1) + (S(n-1) mod n)).

**Result.** Partial. The nine listed values are correct (proved). The general statement is open.

**Argument.** Stable state: if b(N) = x(N + a + 1) with 0 ≤ x < N + a, then b(N) mod (N + a) = x and
b(N+1) = x(N + a + 2), so b grows by x from then on. The nine cases reach a stable state at N = 397, 396, 395,
4, 11, 10, 25, 124, 5 respectively.

Why the general case is hard: write b(n) = k(n+a) + r and e = r − k. While the quotient k stays fixed, e
doubles at each step (e' = 2e), and in general e' ≡ 2e (mod n + a + 1) inside a window of length n + a. The
sequence becomes eventually linear exactly when e reaches 0. Heuristically this happens with probability about
1/n per step, so the stopping time has a tail of order 1/t: for b(1) = 1..100000 (a = 0, A094405 form) every
seed stabilises, the latest at n = 9363863 (seed 31873). Proving that e always reaches 0 is a Collatz-type
problem.

**Evidence.**
- Lean (core): [`A073117.lean`](A073117.lean). `stable`, `adds_of_stable` (the stable-state lemma, all n),
  `listed_values` (the nine listed x by `decide` on the first ≤ 397 terms). Check `tools/leancheck.sh`: OK,
  axioms propext, Quot.sound.
- [`certificate/stabilize.py`](certificate/stabilize.py): stabilisation points of the nine cases.
  [`certificate/seeds.c`](certificate/seeds.c): A094405 seeds 1..100000.
- Outside Lean: the general conjecture (open).

**Review level.** `lean-proof` for the listed values.

**Prior art.** Checked 2026-11-06: entry still says "Conjecture (seems provable)"; web search found no proof;
not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones). The case a = 0,
b(1) = 1 (x = 97) is in the entry (J. W. Layman, 2004, in A094405).

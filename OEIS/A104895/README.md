# OEIS A104895: positions of k ≥ 0 are A048724(k), positions of −k are A065621(k)

**Source.** [A104895](https://oeis.org/A104895), comment: "Conjecture: the positions where 0, 1, 2, 3, ...
appear are given by A048724; the positions where -1, -2, -3, ... appear are given by A065621." (OEIS text,
CC BY-SA 4.0; still stated on 2026-11-05.)

**Reading.** The %N name line reads "a(0)=0; thereafter a(2n) = -2*a(n), a(2n+1) = 2*a(n) - 1". That
recursion gives a(2) = 2, but the data, the b-file (Sloane, n ≤ 20000) and every program in the entry have
a(2) = −2. The data follow a(0) = 0, a(2n) = 2a(n), a(2n+1) = −2a(n) − 1, which is the negated A065620
recursion (the entry's %F a(n) = −A065620(n)). The name line has its two signs swapped. The result below
is for the sequence as its data define it. A048724(k) = k XOR 2k. A065621(k) = (k−1) XOR (2k−1), a formula
in A065621 equal to its k XOR 2(k − (k AND −k)).

**Result.** True. a(n) = k exactly when n = A048724(k) (k ≥ 0), a(n) = −k exactly when n = A065621(k)
(k ≥ 1), and a is a bijection from ℕ onto ℤ.

**Argument.** Write P = A048724, Q = A065621. XOR of 2x + b and 2y + c is 2(x XOR y) + (b XOR c), so
P(2m) = 2P(m), P(2m+1) = 2Q(m+1) + 1, Q(2m+1) = 2P(m) + 1, Q(2m+2) = 2Q(m+1). Strong induction on k with the
recursion gives a(P(k)) = k and a(Q(k+1)) = −(k+1); for example a(P(2m+1)) = −2a(Q(m+1)) − 1 = 2m + 1.
a is injective: a(2m) is even, a(2m+1) is odd, a(n) = 0 only for n = 0, and a(2m) = a(2m') or
a(2m+1) = a(2m'+1) forces a(m) = a(m'). So each value has exactly one position, the one found above.

**Evidence.**
- Lean (Mathlib): [`A104895_mathlib.lean`](A104895_mathlib.lean). `a` is the data recursion (with a fuel
  argument so the kernel can evaluate it); `data_check` compares a(0..77) with the entry's data,
  `printedName_differs` shows the printed %N gives a(2) = 2. Main theorems:
  `A104895_positions_nonneg`: ∀ k n : ℕ, a n = k ↔ n = A048724 k;
  `A104895_positions_neg`: ∀ k n, 1 ≤ k → (a n = −k ↔ n = A065621 k);
  `A104895_bijective`: Function.Bijective a. Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: the data recursion equals the b-file for n ≤ 20000, the printed %N differs first at
  n = 2, the two A065621 formulas agree for k < 10^5, and the positions statement holds for |value| < 10^4.
  Run with the b-file path as argument (not stored here).
- Outside Lean: nothing.

**Review level.** `lean-proof`.

**Prior art.** Partly known, immediate (checked 2026-11-05). A065620 lists A065620(A065621(n)) = n and
A065620(A048724(n)) = −n (Karttunen 2014, stated without proof) and cites Knuth, TAOCP Vol. 2, exercise
4.1.27 for uniqueness of the reversing binary representation; with a = −A065620 these give the conjecture.
No written proof of the A104895 statement found: web search, google-deepmind/formal-conjectures (not
present), otoi-lab/oeis-lean-proofs and epoch-research/LeanOpenProblems-results file trees (no A104895).

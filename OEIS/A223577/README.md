# OEIS A223577 and A223578: A223578(n) = 2·A223577(n) − n + 1

**Source.** [A223577](https://oeis.org/A223577) and [A223578](https://oeis.org/A223578), both by L. Edson Jeffery,
Mar 22 2013, offset 1. With f(m) = ⌊cot(π/(2m))⌋: A223577 lists the positive integers k for which exactly one
negative integer m has −k = f(m); A223578 lists the positive integers k with f(−k−1) < f(−k) < f(−k+1).
Comments: "Conjecture: a(n) = (A223578(n) + n - 1)/2" (A223577) and "Conjecture: a(n) = 2*A223577(n) - n + 1"
(A223578). (OEIS text, CC BY-SA 4.0, checked 2026-11-06.) Scan ids OEIS-A223577 and OEIS-A223578 (one shared
claim; the scan record of A223578 writes "A223568" for A223578, a typo).

**Reading.** f(0) is undefined, so k = 1 is not in A223578 (its data starts at 2); the Lean predicate states
k ≥ 2 explicitly. Offsets: OEIS index n is `n − 1` in `Nat.nth`.

**Result.** True for all n. Proved by Sela Fried (2025); this directory adds a Lean (Mathlib) proof.

**Argument.**
1. Let c(j) = cot(π/(2j)) and g(j) = ⌈c(j)⌉ for j ≥ 1. Since cot is odd and ⌊−x⌋ = −⌈x⌉, f(−j) = −g(j).
   So A223577 = values v ≥ 1 taken by g exactly once, A223578 = {j ≥ 2 : g(j−1) < g(j) < g(j+1)}.
2. For j ≥ 2, with a = π/(2(j+1)) and b = π/(2j): c(j+1) − c(j) = sin(b−a)/(sin a · sin b) and
   b − a = (2/π)·ab. From x − x³/6 < sin x < x, b ≤ π/4 and b − a ≤ π/12 this gives
   3/5 ≤ c(j+1) − c(j) ≤ 1; also c(1) = 0, c(2) = 1. Hence g steps by 0 or 1, g(j+2) ≥ g(j) + 1 (no value
   taken three times), g(1) = 0, g(2) = 1, and g(j) ≥ (3/5)(j − 1).
3. Counting. Let N(j) = #{i ≤ j : i ∈ A223578}. By induction on j ≥ 1,
   N(j) + j + [g(j+1) = g(j)] = 2g(j) + 1, and #{v ≤ g(j) : v ∈ A223577} = N(j).
   At j = A223578(n): g(j+1) ≠ g(j), N(j) = n and g(j) = A223577(n), so j = 2·A223577(n) − n + 1.
4. Both sets are infinite, since N(j) ≥ 2g(j) − j ≥ (j − 6)/5.

**Evidence.**
- Lean (Mathlib): [`A223577_mathlib.lean`](A223577_mathlib.lean). Definitions `f`, `P77` (A223577), `P78`
  (A223578) transcribe the OEIS names. Theorems `A223578_eq : (nth P78 n : ℤ) = 2·nth P77 n − (n+1) + 1` and
  `A223577_eq : 2·nth P77 n = nth P78 n + (n+1) − 1`; `P78_infinite`, `P77_infinite`; analytic steps
  `incr_ge_two`, `incr`; counting invariants `inv1`, `inv2`.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: propext, Classical.choice, Quot.sound
  (`neg_cases` fewer). No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): recomputes both sequences from the definitions (50-digit
  mpmath), checks the identity for n ≤ 10000 and agreement with both b-files (n ≤ 10000; pass the b-file paths
  as arguments).
- Outside Lean: that `P77`, `P78` transcribe the OEIS definitions (by hand; check.py agrees with the b-files).
- Side finding, outside the conjecture: the A223577 FORMULA line a(n) = floor(cot(Pi/(2*A223578(n)))) fails for
  every n ≥ 2 (for n = 2 it gives ⌊√3⌋ = 1, not 2). The correct form is a(n) = ⌈cot(π/(2·A223578(n)))⌉
  = −f(−A223578(n)) (step 1). check.py reports this.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Sela Fried, "Proof of a conjecture relating A223577 and A223578" (2025,
linked from both entries) and "Proofs of Ten Conjectures From the OEIS", J. Integer Sequences 29 (2026),
Article 26.1.8, pp. 12–14: the same argument (mean value theorem for the step bounds, counting singletons via
#{m ≥ 2 : g(m) ≤ r} = 2r − s(r)). Both entries have stated "The conjecture is true (see Fried link)" since
Oct 11 2025. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs; no Lean proof found.

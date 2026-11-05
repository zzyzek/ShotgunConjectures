# OEIS A195609: first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts

**Source.** [A195609](https://oeis.org/A195609): "Numbers n such that Sum_{i=1..n} A(i) = A(n)*A(n+1)/4, where
A(n) = A000069(n)" (odious numbers, offset 1, A(1) = 1). Comment by V. Shevelev (2011): "Conjectures: 1) there are
only 3 different first differences 1,4,6; 2) the sequence contains either isolated series of terms, e.g.,
{9},{23},{33},{39},..., or series of 3 consecutive integers, e.g., {3,4,5}, {15,16,17}, etc.; 3)the first terms m
of every series satisfy the condition A(m+1)-A(m-1)=5, where A(n)=A000069(n)." (OEIS text, CC BY-SA 4.0; fetched
2026-11-05, unchanged since Dec 2019.) Twin of [A195608](../A195608/README.md) (evil numbers).

**Reading.** As for A195608: S = {n ≥ 1 : 4·Σ_{i≤n} A(i) = A(n)A(n+1)}, a series is a maximal run of consecutive
integers in S (singletons included), 1) next element is n + 1, n + 4 or n + 6, 2) [a, b] ⊆ S with a − 1, b + 1 ∉ S
gives b ∈ {a, a + 2}, 3) m ∈ S, m − 1 ∉ S gives A(m+1) − A(m−1) = 5. Here min S = 3, so 3) needs no exception.

**Result.** All three conjectures are true. Closed form, with t the Thue–Morse sequence:
S = {2j+1 : t(j) = 1} ∪ {2j+2 : t(j) = t(j+1) = 1}. For m ∈ S, A(m+1) − A(m−1) is 5 if m starts its series and
4 otherwise.

**Argument.** A(k+1) = 2k + u(k) with u = 1 − t, the indicator of evil numbers shifted by one: the n-th odious number
is the (n−1)-th zero of u. u has the same recursions u(2j) = u(j), u(2j+1) = 1 − u(j) (only u(0) = 1 differs), so
Σ_{k<2j} u(k) = j and the A195608 argument goes through word for word with t replaced by u. The Lean file proves
everything once for any 0/1 sequence with these two recursions (`TMLike`) and instantiates it twice. The odious
closed form was derived this way and checked numerically before the proof (n ≤ 400000, and against the b-file).

**Evidence.**
- `certificate/check.py` (same script as A195608): direct computation for n ≤ 400000, closed form, b-file (10000
  terms), conjectures 1)–3) and the sharper form.
- Lean (Mathlib): [`../A195608/A195608_mathlib.lean`](../A195608/A195608_mathlib.lean) (shared file). Definitions:
  `odious n = Nat.nth (fun k => tm k = 1) (n - 1)`, `A195609set = {n | 1 ≤ n ∧ 4 * ∑ i ∈ Icc 1 n, odious i =
  odious n * odious (n + 1)}`; `odious_values`, `A195609_values` check against OEIS by `decide`. Theorems:
  `A195609_closed_form`, `A195609_conj1`, `A195609_conj1_occur` (17 → 23, 5 → 9, 3 → 4), `A195609_conj2`,
  `A195609_conj3` (m ∈ S, m − 1 ∉ S → odious (m+1) − odious (m−1) = 5), `A195609_conj3_iff`. Axioms: propext,
  Classical.choice, Quot.sound. Nothing outside Lean.

**Review level.** `lean-proof`.

**Prior art.** Same search as A195608 (2026-11-05): OEIS entries still say "Conjectures"; no proof found in the
web search, arXiv:2503.04122, arXiv:2608.11941 or google-deepmind/formal-conjectures.

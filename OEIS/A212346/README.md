# OEIS A212346: a(n) = (n+3)(n^2-4)/6 for n >= 3

**Source.** [A212346](https://oeis.org/A212346) (N. J. A. Sloane, 2012): coefficient of x^0 in the marked mesh
pattern generating function Q_{n,132}^{(0,4,0,0)}(x). Comment: "Conjecture stated in Formula holds through a(35)";
formula: "Conjecture: this appears to equal (n+3)(n^2-4)/6 for n >= 3". (OEIS text, CC BY-SA 4.0, revision #34 of
Nov 05 2025, checked 2026-11-06.)

**Reading.** Q_{n,132}^{(0,4,0,0)}(x) = sum over 132-avoiding permutations s of 1..n of x^m, m = number of entries
of s with at least 4 larger entries to their left (quadrant II). So a(n) counts 132-avoiding permutations in which
every entry has at most 3 larger entries to its left.

**Result.** True: a(n) = (n+3)(n^2-4)/6 for every n >= 3. Barker's recurrence and g.f. in the entry follow.

**Argument.** Let N_k(n) count 132-avoiding permutations of length n in which every entry has fewer than k larger
entries to its left (a = N_4).
1. *Decomposition.* In a 132-avoider with n at position i+1, every entry left of n exceeds every entry right of n.
   The left block (size i) and right block (size n-1-i) are arbitrary 132-avoiders; a left entry's larger-left
   entries are those inside the left block; a right entry has the i left entries, n, and its larger-left entries
   inside the right block. Hence N_k(0) = 1, N_0(n) = 0 for n >= 1, and
   N_k(n) = sum_{i=0}^{n-1} N_k(i) N_{k-1-i}(n-1-i). (This is the x = 0 case of the generating function theorem for
   Q^{(0,k,0,0)}_{132} of Kitaev, Remmel and Tiefenbruck, which the entry's Mathematica program transcribes.)
2. *Closed forms.* Terms with i >= k and a nonempty right block vanish, so for n >= k-1:
   N_k(n+1) = N_k(n) + sum_{i<k-1} N_k(i) N_{k-1-i}(n-i). This gives N_1(n) = 1; N_2(n) = n (n >= 1);
   N_3(n+1) = N_3(n) + n + 1 for n >= 2, so 2N_3(n) = n^2 + n - 2 (n >= 2); and for n >= 3
   N_4(n+1) = N_4(n) + N_3(n) + (n-1) + 2 with N_4(3) = 5. Induction gives 6N_4(n) = (n+3)(n^2-4) for n >= 3, since
   (n+4)((n+1)^2-4) - (n+3)(n^2-4) = 3(n^2+n-2) + 6(n-1) + 12.

**Evidence.**
- Lean (Mathlib): [`A212346_mathlib.lean`](A212346_mathlib.lean). `N k n` is defined by the recursion of step 1;
  main theorem `A212346.A212346_formula : 3 ≤ n → 6 * N 4 n = (n + 3) * (n * n - 4)`, via `step`, `N1`, `N2`, `N3`,
  `N4_rec`, `N4_poly`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/brute.py`](certificate/brute.py): brute force over all permutations for n <= 10 agrees with the
  recursion; the recursion reproduces the 36 data terms a(0..35) and the formula for 3 <= n <= 35; exit 0.
- Outside Lean: step 1, that the recursion counts the permutations (the decomposition; also a published theorem
  and checked by brute force for n <= 10).

**Review level.** `lean-proof` for the recursion-to-formula step; `rechecked` for the decomposition.

**Prior art.** Checked 2026-11-06. S. Kitaev, J. Remmel, M. Tiefenbruck, Quadrant marked mesh patterns in
132-avoiding permutations, Pure Math. Appl. (PU.M.A.) 23 (2012) 219-256 (arXiv:1201.6243), give the generating
function Q^{(0,k,0,0)}_{132}(t,x) whose x = 0 specialisation is rational, so the formula was implied by that
theorem; the entry still lists it as a conjecture. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.

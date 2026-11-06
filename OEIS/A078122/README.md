# OEIS A078122: row sums of the M^3-shift matrix are the partitions of 3^n into powers of 3

**Source.** [A078122](https://oeis.org/A078122) (Paul D. Hanna): "Infinite lower triangular matrix, M, that satisfies
[M^3](i,j) = M(i+1,j+1) for all i,j>=0 ... with M(0,k)=1 and M(k,k)=1 for all k>=0." Comment: "Conjecture: the
sum of the n-th row equals the number of partitions of 3^n into powers of 3 (A078125)." Formula line, also
marked conjecture: "M(n, k) = the coefficient of x^(3^n - 3^(n-k)) in the power series expansion of
1/Product_{j=0..n-k}(1-x^(3^j)) whenever 0<=k<n". (OEIS text, revision #10 of Mar 17 2023, checked 2026-11-06.)

**Reading.** "M(0,k)=1" is read as M(k,0) = 1 (first column of ones), as the data 1; 1,1; 1,3,1; 1,12,9,1 show.
Such an M is unique: column 0 and the diagonal are given, and row i+1 (columns ≥ 1) is row i of M^3, which only
involves rows ≤ i of M.

**Result.** True, together with the formula line. M(n,k) is the number of partitions of 3^n into powers of 3
whose largest part is exactly 3^(n-k); summing over k = 0..n gives all partitions of 3^n into powers of 3. The
same argument works for every base m ≥ 2 (Hanna's M^2 and M^4 analogues A078121 and A078536 with partitions of
2^n and 4^n), checked numerically below.

**Argument.** Let N(n,k) (0 ≤ k ≤ n) count partitions of 3^n into powers of 3 with largest part 3^(n-k), and
N(n,k) = 0 for k > n. Then N(n,0) = N(n,n) = 1. It remains to show [N^3](i,j) = N(i+1,j+1); uniqueness then gives
M = N.

1. *Splitting.* Take a partition of 3^(i+1) into powers of 3 with largest part 3^(i-j) ≤ 3^i, parts listed in
   decreasing order. Before a part 3^r is added, the running sum is a multiple of 3^r (all earlier parts are), so
   the running sums never jump over a multiple of 3^i. Hence the list splits uniquely into three consecutive
   blocks A, B, C (largest parts first), each summing to 3^i, with min A ≥ max B and min B ≥ max C. Conversely
   any such triple concatenates to such a partition, and its split returns the triple.
2. *Counting the blocks.* Let max C = 3^(i-a) and max B = 3^(i-b), so i ≥ a ≥ b ≥ j. C is a partition of 3^i
   with largest part 3^(i-a): N(i,a) choices. B has all parts ≥ 3^(i-a), so B / 3^(i-a) is a partition of 3^a
   with largest part 3^(a-b): N(a,b) choices. A / 3^(i-b) is a partition of 3^b with largest part 3^(b-j):
   N(b,j) choices. So N(i+1,j+1) = Σ_{a,b} N(i,a) N(a,b) N(b,j) = [N^3](i,j).
3. N(n,k) = [x^(3^n - 3^(n-k))] 1/Π_{t=0..n-k}(1 - x^(3^t)) (remove one copy of the largest part), which is the
   formula line, and Σ_k N(n,k) = A078125(n).

**Evidence.**
- Lean (Mathlib): [`A078122_mathlib.lean`](A078122_mathlib.lean). Partitions of S into powers 3^e (lo ≤ e ≤ hi)
  are counted as weakly decreasing exponent lists (`cnt`); `A078125 n = cnt (3^n) (3^n) 0`. `IsA078122 M` states
  the entry's definition (lower triangular, M k 0 = M k k = 1, M(i+1,j+1) = Σ_{a,b ≤ i} M i a M a b M b j, which is
  [M^3](i,j) for lower triangular M). Main theorems `A078122_rowsum : IsA078122 M → Σ_{k ≤ n} M n k = A078125 n`
  and `A078122_formula` (the entry's formula line); `N_spec` shows such an M exists, `eq_N` that it is unique.
  Route: `split` (step 1, by strong induction on the block sum), `scale`/`scaleE` (rescaling), `splitE`,
  `N_cube` (step 2: two splits and a bijection of index pairs). Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py) builds M from its definition and compares it entrywise with N for
  bases 2, 3, 4 (rows 0..12, 0..9, 0..7), with the b-file ([`certificate/b078122.txt`](certificate/b078122.txt),
  first 55 entries) and the row sums with A078125 ([`certificate/b078125.txt`](certificate/b078125.txt)).
- Outside Lean: the base-2 and base-4 analogues (A078121, A078536), checked numerically only; agreement of the
  Lean definitions with the data terms (check.py).

**Review level.** `lean-proof`.

**Prior art** (2026-11-06). OEIS A078122 (rev. #10), A078125, A078121, A078536: conjectures, no proof; web search
(m-ary partition matrices: Flowers et al. 2018, Sellers' part frequency matrices, Stefluk-Zatorsky
parapermanents) found no statement of the shift identity; google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs: no file. The block-split argument is ours.

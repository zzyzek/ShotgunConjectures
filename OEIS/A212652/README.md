# OEIS A212652: a(n) = min of d + (h-1)/2 over n = d*h with h odd, and n lies in row a(n) of A209260

**Source.** [A212652](https://oeis.org/A212652) (offset 1), Max Alekseyev (2008): a(n) is the least positive
integer M such that n = T(M) - T(k) for an integer k with 0 <= k <= M, T = A000217. The scan record (from the
OEIS wiki conjecture list) quotes L. Edson Jeffery's conjectures: a(n) = min B_n, where B_n is the set of
integers d + (h-1)/2 with n = d*h (h odd), and n appears in row a(n) of [A209260](https://oeis.org/A209260).
A209260 Conjecture 2 (Jeffery, Feb 13 2013) adds that n appears in row b of [A141419](https://oeis.org/A141419)
for every b in B_n. The entry now lists a(n) = Min_{odd d|n} (n/d + (d-1)/2) as a formula and keeps "Conjecture:
n appears in row a(n) of A209260". A later comment (O. E. Pol, Jan 07 2025) conjectures that a(n) is the smallest
largest part over the partitions of n into consecutive parts. (OEIS text, CC BY-SA 4.0, A212652 revision #84 of
Jan 11 2025, checked 2026-11-06.)

**Reading.** A141419 row r is T(r) - T(r-k), 1 <= k <= r. A209260 row r is row r of A141419 with the entries
already present in an earlier row of A141419 removed (the construction stated in A209260; certificate/check.py
reproduces the A209260 b-file, 100 rows, this way). "d + (h-1)/2 is integral" means h odd.

**Result.** All true, for every n >= 1:
- a(n) = min over odd h | n of n/h + (h-1)/2;
- n lies in row M of A141419 iff M = n/h + (h-1)/2 for some odd h | n;
- n lies in row a(n) of A209260 and in no other row;
- a(n) is the least largest part of a partition of n into consecutive positive parts.

**Argument.** n = T(M) - T(k) with k < M means 2n = L * S with L = M - k >= 1 and S = M + k + 1 = 2k + L + 1;
L + S = 2M + 1 is odd, so exactly one of L, S is odd, and M = (L + S - 1)/2.
- L odd: h = L, n/h = S/2, M = n/h + (h-1)/2.
- L even: h = S, n/h = L/2, M = n/h + (h-1)/2.
Conversely, for n = d*h with h = 2j+1 put M = d + j, and k = d - j - 1 if h <= 2d (L = h), k = j - d if h > 2d
(L = 2d); both give T(M) - T(k) = n. So the set of M that represent n is exactly B_n, which gives the formula and
the A141419 statement. Since n is in row M of A141419 iff M represents n, the first row of A141419 containing n is
row a(n), so n survives in row a(n) of A209260 and is removed from every later row. Finally (k+1) + ... + M =
T(M) - T(k), so Pol's reading is the definition.

**Evidence.**
- Lean (Mathlib): [`A212652_mathlib.lean`](A212652_mathlib.lean). Definitions: `T`, `Rep n M` (1 <= M and
  n = T M - T k for some k <= M), `a n = Nat.find`, `row141419`, `row209260`. Theorems: `A212652_formula` (for
  n >= 1: a n <= n/h + (h-1)/2 for every odd h | n, with equality for some odd h | n), `mem_row141419_iff`,
  `A212652_row209260` (n in row a(n) of A209260, and in no other row), `A212652_consecutive` (Pol).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: propext, Classical.choice, Quot.sound.
  No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): the formula matches the A212652 b-file (n <= 10000), the
  definition matches for n <= 2000, the A209260 construction matches its b-file (100 rows), and n <= 100 lies in
  row a(n).
- Outside Lean: none beyond reading the definitions (agreement with the b-files is checked by check.py only).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. A209260 links Hartmut F. W. Hoft, "Proof of Conjecture 2" (a209260_2.pdf,
comment of Apr 14 2016), which proves the row statement and the min formula; A212652 still marks the row
statement "Conjecture". Not in google-deepmind/formal-conjectures (no 212652 or 209260 file in the tree at HEAD)
or otoi-lab/oeis-lean-proofs. No Lean proof found before this one.

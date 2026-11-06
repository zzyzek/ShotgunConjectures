# OEIS A078128: partitions into cubes > 1 — a(n) → ∞ with explicit b(k)

**Source.** [A078128](https://oeis.org/A078128) (offset 1), "Number of ways to write n as sum of cubes > 1".
Comment (Reinhard Zumkeller): "Conjecture (lower bound): for all k exists b(k) such that a(n)>k for n>b(k); see
b(0)=A078129(83)=154 and b(1)=A078130(63)=218." (OEIS text, CC BY-SA 4.0; still marked conjecture in revision #18,
Jun 17 2025, checked 2026-11-06.)

**Result.** True: a(n) ≥ m + 1 whenever n ≥ 216m + 182, so b(k) = 216k + 181 works. The quoted values are sharp:
a(154) = 0 and a(n) ≥ 1 for n > 154; a(218) = 1 and a(n) ≥ 2 for n > 218. (Numerically the least b(k) are
154, 218, 255, 282, 319, 335 for k = 0..5; 216k + 181 is only an upper bound.)

**Argument.** Every r ≥ 182 is 8x + 27y (y = 3r mod 8; 181 is the Frobenius number of 8 and 27). For
n ≥ 216m + 182 write n − 216m = 8x + 27y; the partitions with x + 27j eights and y + 8(m − j) twenty-sevens,
j = 0..m, are m + 1 different partitions of n into cubes > 1 (they differ in the number of 8s). For the sharp values:
for n < 512 the parts are among 8, 27, 64, 125, 216, 343 and a partition is fixed by its multiplicities, so a(n) is a
coin-change count, evaluated for n < 398; the bound above covers n ≥ 182 (k = 0) and n ≥ 398 (k = 1).

**Evidence.**
- Lean (Mathlib): [`A078128_mathlib.lean`](A078128_mathlib.lean), namespace `A078128`. `a n` = number of
  `p : Nat.Partition n` whose parts are all cubes k³ with k ≥ 2 (the OEIS definition). Theorems:
  `A078128_conj : ∀ k, ∃ b, ∀ n, b < n → k < a n`; `a_lower` (216m + 182 ≤ n → m + 1 ≤ a n); `A078128_b0`
  (a 154 = 0 ∧ ∀ n > 154, 0 < a n); `A078128_b1` (a 218 = 1 ∧ ∀ n > 218, 1 < a n). Route: `mem_msets`,
  `card_msets`, `a_eq_ways`, kernel evaluation (`decide +kernel`) of coin-change counts.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: at most propext, Classical.choice, Quot.sound.
  No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): recomputes a(n) to 20000, checks the 8/27 bound, prints the least
  b(0..5), and checks the b-file b078128.txt (n ≤ 10000; all agree, run 2026-11-06).
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry still says "Conjecture". The ingredients are classical and on adjacent
entries: A078129 (Adams-Watters 2006: every n > 181 is a sum of 8s and 27s), A078130 (Irvine 2025: b(1) = 218).
The growth a(n) ≥ number of (x, y) with 8x + 27y = n ≈ n/216 is immediate from these; Kotesovec's asymptotic in the
entry (stated without proof) also implies it. Not in google-deepmind/formal-conjectures (clone of 2026-11-05) or
otoi-lab/oeis-lean-proofs (clone of 2026-10-13).

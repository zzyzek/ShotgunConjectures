# OEIS A122957: "except for 1,2,3,4, this is the nonzero values of A066362" is false

**Source.** [A122957](https://oeis.org/A122957), numbers n such that φ(m) ≥ φ(n) for every m > n. Comment:
"Conjecture: except for 1,2,3,4, this is the nonzero values of A066362." (OEIS text, CC BY-SA 4.0, rev #6 of
Mar 30 2012, read 2026-11-06.) [A066362](https://oeis.org/A066362)(n) is the least k > n with φ(k) < φ(n),
or 0 if there is none. The entry's cross-reference line reads "zeros of A066362".

**Reading.** Literal: the set of nonzero values {A066362(n) : n ≥ 1} \ {0} equals A122957 \ {1, 2, 3, 4}.

**Result.** False. A066362(21) = 22 (φ(21) = 12, φ(22) = 10), but 22 is not in A122957 (φ(24) = 8 < 10).
The nonzero values outside A122957 below 5000 begin 22, 26, 28, 32, 34, 38, 40, 44, ...

What holds:
- A122957 is exactly the zero set of A066362 (by the two definitions; 1, 2, 3, 4 included). This is the
  cross-reference "zeros of A066362".
- One inclusion of the comment holds numerically: every term of A122957 other than 1, 2, 3, 4 below 5000 is a
  nonzero value of A066362 (`certificate/check.py`). Not proved here.

**Argument.** φ(21) = φ(3)φ(7) = 12, φ(22) = 10, φ(24) = 8. The least k > 21 with φ(k) < 12 is 22, and
24 > 22 has φ(24) < φ(22). Zero set: A066362(n) = 0 iff no k > n has φ(k) < φ(n), which is the definition of
A122957.

**Evidence.**
- Lean (Mathlib): [`A122957_mathlib.lean`](A122957_mathlib.lean), namespace `A122957`. `A122957_misstated`
  (A066362 21 = 22 and 22 ∉ A122957, with `Nat.totient` and `decide`), `A066362_eq_zero_iff` (zero set = A122957,
  all n). Check `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): both inclusions for n ≤ 5000.
- Outside Lean: only the reading of the two OEIS definitions.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: the entry is unchanged since 2012 and still states the conjecture; not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones). The counterexample comes
directly from the data of A066362 (a(21) = 22).

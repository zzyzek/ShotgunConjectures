# OEIS A179873, A179874: integral antiharmonic means of the units mod h are odd and nondecreasing

**Source.** [A179873](https://oeis.org/A179873) (Jaroslav Krizek, 2010): values of the antiharmonic mean
B(h) = Σk²/Σk over the k < h with gcd(k, h) = 1, for the h with B(h) an integer ([A179871](https://oeis.org/A179871)).
Comment: "Conjecture: nondecreasing sequence of odd numbers." [A179874](https://oeis.org/A179874): "Possible values of
A179873(m) in increasing order"; comment: "Conjecture: a(n) = sequence of odd numbers." (OEIS text, CC BY-SA 4.0,
A179873 revision #21 of May 25 2025, A179874 revision #10 of Jan 09 2025, checked 2026-11-06.)

**Reading.** B(h) is taken over 1 ≤ k ≤ h with gcd(k,h) = 1 (for h ≥ 2 the same as k < h; for h = 1 this gives
B(1) = 1, the entry's first term). "Sequence of odd numbers" means every term is odd (A179874 omits 5, 9, ...).

**Result.** Both true: whenever B(h) is an integer, 3B(h) = 2h ± 1, so B(h) is odd, and B is nondecreasing along
A179871. More precisely B(h) ∈ ℤ iff h is squarefree and B(h) = (2h + (−1)^ω(h))/3 is an integer.

Side note: A179874's data lists 151 twice ("..., 145, 151, 151, 153, ..."); the distinct values contain 151 once and
otherwise agree with the data.

**Argument.**
1. For n ≥ 2, Σ_{units} k = nφ(n)/2 and Σ_{units} k² = (2n²φ(n) + n·Π_{p|n}(1−p))/6 (Möbius inversion of
   Σ_{k<n} k^r = Σ_{d|n} d^r Σ_{units mod n/d} j^r, with Σ_{d|n} μ(d)d = Π(1−p); classical, see A053818).
2. So 3φ(h)B(h) = 2hφ(h) + Π(1−p), and Π(1−p) = ±Q with Q = Π(p−1). If B(h) = t ∈ ℤ then φ(h) | Q; since
   φ(h)·Πp = h·Q and Πp | h, this forces Q = φ(h) (h squarefree), and 3t = 2h ± 1.
3. 2h ± 1 is odd, so t is odd; for h < h', 3t ≤ 2h + 1 ≤ 2h' − 1 ≤ 3t'.

**Evidence.**
- Lean (Mathlib): [`A179874_mathlib.lean`](A179874_mathlib.lean). B(h) is defined as in the entry (Finset sums over
  `Icc 1 h` with `Nat.Coprime`). Main theorems `B_odd`, `B_mono`, `three_B`; route `sum_moebius_mul_self`,
  `inversion`, `F_one`, `F_two`, `B_formula`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms
  propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): for h ≤ 3000, B(h) ∈ ℤ iff h squarefree with 3 | 2h + (−1)^ω, the
  values are odd and nondecreasing, they equal the A179873 b-file ([`certificate/b179873.txt`](certificate/b179873.txt),
  698 terms), and the A179874 data equals the distinct values after deleting the repeated 151.
- Outside Lean: none beyond reading the definitions. Not verified in Lean: agreement with the OEIS data.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The power-sum formula for units is classical (A053818: Brown's formula; Eldar's
2025 PARI program for A179873 uses B(n) = 2n/3 + Π(1−p)/(3φ(n))); A179871 says A179873 consists of "odd positive
integers" without proof. The deduction (squarefreeness, 3B = 2h ± 1) was not found stated. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

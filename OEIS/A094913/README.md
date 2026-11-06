# OEIS A094913: maximal number of distinct nonempty factors of a binary word of length n equals A006697(n) − 1

**Source.** OEIS [A094913](https://oeis.org/A094913) (offset 0): maximal number of distinct nonempty
substrings (factors) of a binary string of length n. Conjecture (V. Jovovic, Sep 19 2005):
"a(n) = A006697(n)-1." (OEIS text, CC BY-SA 4.0; revision #33.) A006697 is the subword complexity ρ_z(n)
(number of distinct factors of length n) of z, the fixed point of a → aab, b → b.

**Result.** True.

**Argument.** Write M(n) = Σ_{i=0..n} min(2^i, n − i + 1).
- A. Flaxman, A. W. Harrow, G. B. Sorkin, Strings with maximally many distinct subsequences and substrings,
  Electron. J. Combin. 11 (2004) R8, Theorem 8, bullets 1–2: a word of length n over d letters has at most
  min(d^m, n − m + 1) distinct factors of length m, and a modified de Bruijn word attains all these bounds at
  once. With d = 2 and m ≥ 1 summed, a(n) = M(n) − 1 (the m = 0 term is the empty word).
- J.-P. Allouche, J. Shallit, On the subword complexity of the fixed point of a → aab, b → b, and
  generalizations, arXiv:1605.02361, Theorem 1: ρ_z(n) = M(n) for n ≥ 0, so A006697(n) = M(n).
  Remark 3 there notes that M(n) is the maximal number of factors of all lengths (empty word included) of a
  binary word of length n, citing Iványi 1987, Shallit 1993 and FHS 2004, and Remark 16 states that this
  confirms Jovovic's conjecture A006697(n) = A094913(n) + 1.

Hence a(n) = M(n) − 1 = A006697(n) − 1.

FHS Theorem 8 bullet 3 also gives a closed form (d^{k+1} − 1)/(d − 1) + C(n − k + 1, 2) with k = ⌊log_d n⌋.
For d = 2 it is wrong at n = 4, 8, 9, 16, 17, 18, 32, ... (n = 4 gives 10, while M(4) = 9); the correct split
point is the largest k with 2^k ≤ n − k + 1, as in Hasler's LambertW formula (AS 2016, Remark 16). The
argument above uses only bullets 1–2.

**Evidence.**
- `certificate/check.py` (a few seconds): brute force over all binary words for n ≤ 16 equals M(n) − 1 and the
  printed terms; ρ_z(n) read from the prefix of z of length 2^17 equals M(n) for n ≤ 16 and matches the printed
  A006697 terms; lists the n ≤ 40 where FHS bullet 3 differs from M(n).
- No Lean file.
- Outside Lean: FHS 2004 Theorem 8 (bullets 1–2) and Allouche–Shallit 2016 Theorem 1.

**Review level.** `rechecked`. Theorem 1, Remark 3 and Remark 16 read in arXiv:1605.02361 v1; Theorem 8 read
in the EJC article. The bound in bullet 1 is immediate (at most d^m words of length m, at most n − m + 1
starting positions).

**Prior art.** Checked 2026-11-05: the entry already links Allouche–Shallit 2016, FHS 2004, Iványi 1987 and
Shallit 1993 (added by J. Shallit, Nov 2015: "Some of the conjectures above are proven in the papers cited"),
but Jovovic's comment is still labelled a conjecture. google-deepmind/formal-conjectures has no file for
A094913; `FormalConjectures/OEIS/6697.lean` states a generating-function conjecture for A006697 (with M(n) as
the known formula), tagged `research solved` with a formal proof at AxiomMath/gdm-formal-conjectures. That
covers A006697 only, not the maximal-factor count.

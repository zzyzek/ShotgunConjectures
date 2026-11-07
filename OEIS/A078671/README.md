# OEIS A078671: a(n) is not monotone for n > 4 (a(25) = 100891 > a(26) = 20382)

**Source.** OEIS [A078671](https://oeis.org/A078671): number of times the n-th prime appears
among the decimal digits of the Fermat number 2^(2^n) + 1. Questions by Ryan Propper
(Jan 04 2008): "Is a(n) monotonically increasing for n > 4? Does lim{n->inf} a(n)/a(n+1) = 0.5?"
(OEIS text, CC BY-SA 4.0).

**Reading.** Occurrences are counted with overlaps (this reproduces every listed term; for
n ≤ 27 the non-overlapping count differs only at n = 26, 20191 against 20382).

**Result.**
1. No: a(25) = 100891 > a(26) = 20382, so a(n) is not monotone for n > 4. The drop is caused by
   prime(26) = 101 having one more digit than prime(25) = 97. The listed data already contains
   both values; recomputed here.
2. The limit question is open. Heuristically a(n) ≈ 0.301·2^n/10^{D(n)} with D(n) the number
   of digits of prime(n), so a(n)/a(n+1) ≈ 1/2 except at the infinitely many n where D jumps,
   where it is ≈ 5 (a(25)/a(26) = 4.95). On that heuristic the limit does not exist.

**Argument.** Direct computation: `certificate/fer.gp` writes the decimal expansion of
2^(2^n)+1 for n ≤ 27 (PARI/GP); `certificate/count.py` counts occurrences of prime(n).
All 27 counts agree with the OEIS data (n = 26: 20382 in 20201783 digits; n = 25: 100891 in
10100892 digits).

**Evidence.** No Lean: the witness is a count over a 20-million-digit string, beyond kernel
evaluation. Outside Lean: the digit counts for n = 25, 26 (PARI `Str` plus Python counting).

**Review level.** `rechecked` (independent recomputation of the listed terms).

**Prior art.** OEIS A078671 (checked 2026-11-07) still shows both questions; its data
(a(26) = 20382) answers the first. google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs: no entry. The second question would follow from (or contradict)
asymptotic counts of fixed digit blocks in 2^(2^n), a normality-type statement for which no
unconditional result is known (compare the open question whether 2^86 is the last power of 2
without a digit 0).

# Coman P127: Poulet numbers P2 = 2*P1 - 1 with P1 Poulet

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 127. Paraphrase: are there Poulet numbers P2 = 2*P1 - 1 with P1 also Poulet, other than 130561 = 2*65281 - 1? The attached infinitude conjecture is conjecture 178 (COM-C178, not settled here).

**Result.** Yes. 31417 = 2*15709 - 1 (31417 = 89*353, 15709 = 23*683) and 41541241 = 2*20770621 - 1. There are 27 such P2 below 10^13.

**Argument.** Direct check.

**Evidence.**
- Lean (Mathlib): [`P127_mathlib.lean`](P127_mathlib.lean), `P127_main`: some P2 ≠ 130561 is `Nat.FermatPsp P2 2` with P2 = 2*P1 - 1 and `Nat.FermatPsp P1 2`; also 130561, 31417, 41541241 individually. Outside Lean: the count 27 below 10^13.
- [`../P126/certificate/scan.py`](../P126/certificate/scan.py) scans the Feitsma-Galway list; output in `../P126/certificate/scan.log`.

**Review level.** `lean-proof` for the answer.

**Prior art.** Verdict `known`. OEIS [A303531](https://oeis.org/A303531) (numbers k with k and (k+1)/2 both base-2 Fermat pseudoprimes, Max Alekseyev, 2018) lists 31417, 130561, 41541241, ...; the P1 values are A298758. Searched: OEIS (terms), google-deepmind/formal-conjectures, otoi-lab/oeis-lean-proofs (2026-11-06).

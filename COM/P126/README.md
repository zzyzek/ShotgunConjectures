# Coman P126: Poulet numbers P = (d^2 + d)/2 with d a prime factor of P

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 126. Paraphrase: are there Poulet numbers P = (d^2 + d)/2, d a prime factor of P, other than 2701 = (73^2 + 73)/2? The attached infinitude conjecture is conjecture 177 (COM-C177, not settled here).

**Result.** Yes. 18721 = (193^2 + 193)/2 = 97 * 193 and 33153 = (257^2 + 257)/2 = 3 * 43 * 257 are base-2 pseudoprimes. There are 7988 such P below 10^13.

**Argument.** Direct check. A sufficient condition explains most examples: if d is a prime with d = ±1 (mod 8) and m = (d + 1)/2 is prime, then P = d*m and P - 1 = ((d - 1)/2)(d + 2) = (m - 1)(2m + 1); 2 is a square mod d, so ord_d(2) divides (d - 1)/2, and ord_m(2) divides m - 1, hence 2^(P-1) = 1 (mod P). Examples: (73, 37), (193, 97).

**Evidence.**
- Lean (Mathlib): [`P126_mathlib.lean`](P126_mathlib.lean), `P126_main`: some P ≠ 2701 is `Nat.FermatPsp P 2` with a prime d, d | P, P = (d^2 + d)/2; also 2701, 18721, 33153 individually. Outside Lean: the count 7988 below 10^13 and the sufficient condition above (not needed for the answer).
- `certificate/scan.py` scans the Feitsma-Galway list ([`data/psp2-annot-below-1e13.txt`](../../DATA.md)); output `certificate/scan.log`. It also produces the P127 data.

**Review level.** `lean-proof` for the answer.

**Prior art.** Verdict `known`. OEIS [A293622](https://oeis.org/A293622) (Fermat pseudoprimes to base 2 that are triangular, Amiram Eldar, 2017) lists 2701, 18721, 33153, ... with indices 73, 193, 257 (prime factors of the terms); its comment cites Rotkiewicz's proof that triangular base-2 pseudoprimes are infinite (that construction does not control whether the index d is prime, so C177 stays open). Coman's own [A214016](https://oeis.org/A214016) (2012) lists 18721 as well. Searched: OEIS (terms and "pseudoprime triangular"), google-deepmind/formal-conjectures, otoi-lab/oeis-lean-proofs (2026-11-06).

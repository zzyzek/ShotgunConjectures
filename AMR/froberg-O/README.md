# AMR froberg-O: periods of the zero-set map φ on F_p[x]: period 6 occurs (partial)

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and from the
other pockets*, Arnold Math. J. 4 (2018), Section 4.3, Problem O, listed via
https://amathr.org/problems/. Paraphrase: φ(f) = Σ_{a ∈ Z(f)} x^a, where Z(f) ⊆ F_p is the zero set
and a is read as an integer in {0, …, p − 1}. For n = 1, which period lengths occur? The paper: the
4-cycle 0 → 1 + x + … + x^{p−1} → x → 1 → 0 for every p; by exhaustive search no other period for
p ≤ 17; a 2-cycle at p = 71; periods are always even (stated as easy).

**Reading.** After one step every state is a 0/1 polynomial, i.e. a set S ⊆ {0, …, p − 1} of
exponents, and φ acts by S ↦ {b ∈ F_p : Σ_{a∈S} b^a = 0} (0^0 = 1).

**Result (partial).**
- Evenness (re-proved, in Lean): 0 ∈ φ(S) iff 0 ∉ S, so membership of 0 alternates along every orbit
  and every period is even.
- Exhaustive census for p ≤ 31: the only cycle is the standard 4-cycle (p = 19, 23, 29, 31 are new;
  p = 29 has 114356 image sets, p = 31 has 199235).
- Period 6 occurs: at p = 1009,
  {472, 553, 786, 868} → {0, 121, 144} → {446, 495} → {0, 74, 150, 578, 615, 707, 904, 1008}
  → {103, 322, 775} → {0, 337, 506, 561, 759, 922, 951} → {472, 553, 786, 868}
  (six distinct states; Lean `cycle1009`, `period_six_1009`). So the known lengths are 2, 4, 6.
- Small-support search: every cycle reached from a set of size ≤ 2 for all primes p ≤ 593, of size
  ≤ 3 for p ≤ 139, of size ≤ 4 for p ≤ 59: periods 2 and 4 only. Random search (200 random starts
  of size 1 to 3 for each of the 382 primes 1000 < p < 4000): 32 cycles of period 2, 2 of period 4
  (p = 1877, 2311, besides the standard one), 1 of period 6 (p = 1009). The small-support
  search found 2-cycles at p = 71, 127, 151 (two), 181, 367, 373, 397, 409, 421 (two), 431, 449; a second, non-standard
  4-cycle at p = 541: {129, 411} → {0, 52, 216, 268, 273, 325, 489} → {120, 133, 529} → {0, 163, 362}
  → {129, 411}.
- Structure: for b = g^j ≠ 0 (g a primitive root), Σ_{a∈S} b^a is the discrete Fourier transform over
  F_p of the indicator of S reduced mod p − 1 (exponents 0 and p − 1 coincide), so φ is "zeros of a
  DFT" followed by j ↦ g^j read as an integer. This mixes the additive and multiplicative structure
  of F_p, which is why the cycles look sporadic.

**Evidence.**
- Lean (core): [`froberg_O.lean`](froberg_O.lean). `cycle71`, `cycle127`, `cycle151`, `cycle541`, `cycle1009`,
  `period_six_1009` (kernel evaluation, `decide +kernel`, no axioms) and `zero_alternates` (0 ∈ φ(S) ↔ 0 ∉ S for S
  without repetitions; axioms propext, Classical.choice, Quot.sound). Checked with
  tools/leancheck.sh, no warnings.
- certificate/phi_exh.c (Gray-code census: all 2^p sets, image bitmap, cycle search from every image;
  output exh.out), certificate/phi_small.c (Brent cycle detection from every set of size ≤ K;
  outputs k2.out, k2b.out, k3.out, k4.out), certificate/phi_rand.c (random starts; rand.out).
- Outside Lean: the census and the searches (C programs); the period-6 cycle itself is checked in Lean. The paper's p ≤ 17 claim and the p ≤ 23
  triage check are reproduced.

**Review level.** `lean-witness` for the listed cycles and the evenness lemma; the census is
`agent`.

**Prior art.** Searched 2026-11-07: web search for the map and the values; google-deepmind/
formal-conjectures (no entry). Only the paper's data (p ≤ 17, the 2-cycle at 71) found.

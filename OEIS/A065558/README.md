# OEIS A065558: a(2n) = 2 psi(n) (maximal irreducible degree of GL_2(Z/2nZ))

**Source.** [A065558](https://oeis.org/A065558): a(n) is the maximal degree of an irreducible complex representation of
G_n = GL_2(Z/nZ). The entry notes that a is multiplicative and a(p) = p + 1 for odd primes p. Conjecture (Ralf
Stephan, Mar 26 2004): a(2n) = 2*A001615(n), with A001615 the Dedekind psi function psi(n) = n prod_{p | n} (1 + 1/p).
Data: n = 1..24. (OEIS text, checked 2026-11-06.)

**Result.** True. Precisely: a(p^r) = p^(r-1)(p+1) for every prime power p^r except a(2) = 2, so a(n) = psi(n) for
odd n, and a(2n) = 2 psi(n) for all n >= 1.

**Argument.**
1. Multiplicativity: G_(mn) = G_m x G_n for coprime m, n (CRT), and irreducibles of a direct product are tensor
   products, so maximal degrees multiply.
2. Odd p: the irreducible representations of GL_2(Z/p^r) (p odd) are known (Nagornyi 1976; also Kutzko, Stasinski
   arXiv:0807.4684): twists of representations of GL_2(Z/p^(r-1)) and new ones of degrees p^(r-1)(p+1),
   p^(r-1)(p-1), p^(r-2)(p^2-1). Hence a(p^r) = p^(r-1)(p+1).
3. p = 2, r >= 2: a(2^r) = 3 * 2^(r-1). Let G = GL_2(Z/2^r), K_j = 1 + 2^j M_2 (mod 2^r), l = ceil(r/2), N = K_l
   (abelian). Characters of N are psi_beta(1 + 2^l x) = exp(2 pi i tr(beta x)/2^(r-l)), beta in M_2(Z/2^(r-l)),
   permuted by conjugation. For an irreducible pi containing psi_beta, Clifford theory gives
   dim pi = [G : G_beta] dim sigma, with G_beta the stabiliser and sigma an irreducible of G_beta over psi_beta.
   - beta scalar mod 2 (beta = a + 2 beta'): psi_(aI) = chi(det) on N for a character chi of (Z/2^r)^*
     (det(1 + 2^l x) = 1 + 2^l tr x mod 2^r), so pi (x) chi(det)^(-1) is trivial on K_(r-1) and has the degree of an
     irreducible of GL_2(Z/2^(r-1)): at most max(2, 3 * 2^(r-2)) by induction.
   - beta not scalar mod 2: beta-bar is cyclic, its centraliser is F_2[beta-bar], and G_beta = C K_(r-l) with
     C = (Z/2^r[beta~])^*, beta~ a lift. With |G| = 3 * 2^(4r-3) and |C| = 2^(2r-2), 3 * 2^(2r-2), 2^(2r-1) in the
     split (char. poly x(x+1)), irreducible (x^2+x+1) and nilpotent (x^2 or (x+1)^2) cases,
     [G : G_beta] = 3 * 2^(2r-1-2l), 2^(2r-1-2l), 3 * 2^(2r-2-2l).
     psi_beta extends to a linear character Theta of M = C K_l (C abelian and stabilises psi_beta), so every sigma
     lies in Ind_M^(G_beta) Theta' and dim sigma <= [G_beta : M], which is 1 for r even and 4 for r odd.
     r even: dim pi = [G : G_beta] <= 3 * 2^(r-1). r odd (r >= 3): irreducible case <= 2^(r-2) * 4 = 2^r, nilpotent
     case <= 3 * 2^(r-3) * 4 = 3 * 2^(r-1); split case: C = 1 + 2 Z[beta~] (units of Z/2^r x Z/2^r are odd), so with
     j = 1 + 2^(l-1) x and c = 1 + 2u, c^(-1) j c j^(-1) = 1 + 2^l c^(-1)[x, u] mod 2^r and
     tr(beta c^(-1) [x, u]) = 0 because beta, c, u commute. Hence M is normal in G_beta, every extension Theta is
     G_beta-stable, G_beta/M is (Z/2)^2, and Theta([j1, j2]) = (-1)^tr(beta-bar [x1, x2]) is a non-degenerate
     commutator form on it; so sigma is unique of degree 2 and dim pi = 3 * 2^(r-2) * 2 = 3 * 2^(r-1).
   - Lower bound: split beta-bar = diag(0, 1) gives degree exactly 3 * 2^(r-1) (r even: dim sigma = 1; r odd: 2).
   So a(2^r) = 3 * 2^(r-1) = psi(2^r) for r >= 2, and a(2) = 2 (GL_2(F_2) = S_3).
4. For n = 2^j m, m odd: a(2n) = a(2^(j+1)) a(m) = 3 * 2^j psi(m) = 2 psi(2^j) psi(m) = 2 psi(n) for j >= 1, and
   a(2m) = 2 psi(m) for j = 0.

**Evidence.** Paper argument; `lean_status: none` (Clifford theory and the classification for odd p are not in
Mathlib). The entry's data a(1..24) agree, including the 2-power terms a(2), a(4), a(8), a(16) = 2, 6, 12, 24 (r = 3 is
an odd-r split case). GAP 4 character degrees (`CharacterDegrees` of GL_2(Z/n) as a permutation group; scripts and outputs in
[`certificate/`](certificate/), each run in a 2 GB scope, exit codes recorded):
- [`small.out`](certificate/small.out) (`run_small.g`): full degree lists for n = 2..24, maxima equal the entry's data.
- [`pow2.out`](certificate/pow2.out), [`pp.out`](certificate/pp.out): a(32) = 48, a(64) = 96, a(128) = 192, so
  a(2^r) = 3 * 2^(r-1) for 2 <= r <= 7 (r = 2..4 also in small.out); odd prime powers a(25) = 30, a(27) = 36
  (= p^(r-1)(p+1)). GL_2(Z/256) did not finish in about 10 minutes and GL_2(Z/49) timed out (`more_partial.out`, `pp.out`,
  exit 124).
- [`even.out`](certificate/even.out) (`even_one.g`, 120 s per n): a(2n) = 2 psi(n) for 2n = 2..32, 36, 48, 54. The other
  2n <= 60 timed out (exit 124). The script's psi(1) evaluates to 2 (GAP's Factors(1) = [1]), so the line for 2n = 2
  prints ok=false; the true value 2 psi(1) = 2 equals a(2) = 2.
- [`split_check.py`](certificate/split_check.py): the commutator facts of the odd-r split case for r = 3, 5, 7.
Outside Lean: all. Checked by GAP: the maxima for the n listed above. Argument only: a(2^r) for r >= 8, odd p (cited
from Nagornyi), and the general identity a(2n) = 2 psi(n).

**Review level.** `rechecked` (GAP character tables for the cases listed; the general p = 2 step is a new write-up, odd p cited).

**Prior art.** Checked 2026-11-06: A065558 (still conjecture, no links), Nagornyi (Zap. Nauchn. Sem. LOMI 1976; J. Soviet
Math. 1981) for odd p, Stasinski arXiv:0807.4684 (survey of Kutzko/Hill/Nagornyi), Q. Wen's Alberta thesis (odd p;
says p = 2 follows by modifying the method, without details), web search, google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs (no entry). The p = 2 degrees are likely implicit in Nobs–Wolfart's work on SL_2(Z_2) but I
did not find a statement for GL_2(Z/2^r).

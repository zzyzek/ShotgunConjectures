# OEIS A217396: 2^k − 2 twice a triangular or 3/2 a tetrahedral number only for k = 1, 2, 3, 5, 7, 13

**Source.** OEIS A217396 (Raphie Frank, 2012), data 1, 2, 3, 5, 7, 13. Conjecture (OEIS wiki
Talk:Conjectures/List, from the entry's former comments): this is the complete set of k with
2^k − 2 (a) twice a triangular number (A076046), or (b) 3/2 times a tetrahedral number (A217482),
"true to at least 1.41·10^1505" (C. R. Greathouse IV, Physics Forums, Nov 2010). Current entry
(checked 2026-11-06, #70, Aug 14 2026): renamed in June 2025 to "Prime indices of Euler's lucky
numbers"; the conjecture comment is no longer in the entry.

**Reading.** Under the current name the sequence is finite and complete by the classification of
Euler's lucky numbers (Rabinowitsch; Heegner–Baker–Stark class number one), so the entry itself
no longer states a conjecture. We settle the original characterization (a) ∨ (b), k ≥ 1.

**Result.** True. (a) 2^k − 2 = n(n+1) iff (2n+1)^2 + 7 = 2^(k+2), the Ramanujan–Nagell equation;
Nagell (1948): k ∈ {1, 2, 3, 5, 13}. (b) 2(2^k − 2) = 3·j(j+1)(j+2)/6 iff y^3 − y + 8 = 2^(k+2)
with y = j + 1. **New:** the only integer solutions of y^3 − y + 8 = 2^m are
y ∈ {−2, −1, 0, 1, 3, 5, 8} (m = 1, 3, 3, 3, 5, 7, 9), so (b) holds exactly for k ∈ {1, 3, 5, 7}.
The union is {1, 2, 3, 5, 7, 13}. This also proves the conjecture in OEIS A217482 (the tetrahedral
numbers T with (3/2)T + 2 a power of 2 are 0, 4, 20, 84).

**Argument for (b).** K = Q(α), α^3 − α + 8 = 0: discriminant −431, signature (1,1), class
number 1, [O_K : Z[α]] = 2, fundamental unit ε = −6α − 13, and (2) = P1 P2 P3 with generators
π1 = (α^2 + α − 2)/2, π2 = (α^2 + 3α + 2)/2, π3 = α + 2, π1π2π3 = 2ε (`s1.gp`, `dep.gp`).
1. N(y − α) = f(y) = 2^m, so y − α = ±ε^a π1^b1 π2^b2 π3^b3 with b1 + b2 + b3 = m. In the
   2-adic embeddings v_Pi(y − α) = v_2(y − θ_i), θ_i the 2-adic roots of f, and the pairwise
   differences of the θ_i have 2-adic valuations 0, 0, 1. So two of the b_i are in {0, 1}.
2. Real embedding α1 ≈ −2.166: Λ = 3 log|y − α1| − m log 2 = 3a log|ε1| + Σ b_i l_i with
   l_i = 3 log|π_i(α1)| − log 2, and for y ≥ 10, 0 < Λ = 2 log(|y − α1|/|y − α2|) < 8·2^(−m/3)
   (α2 complex).
3. Matveev's lower bound (n = 3, D = 3; γ = |ε1|, |π_i(α1)|^3/2 and the product of the two small
   factors) gives m < 3.4·10^17 in each of the 12 cases (`baker.gp`).
4. Dujella–Pethő reduction (continued fractions of log|ε1|/l_i; the four cases where both small
   exponents are 1 become homogeneous through l1 + l2 + l3 = 3 log|ε1| and use Legendre's bound
   with the largest partial quotient) lowers this to m ≤ 207, 60, 51, 50 in four rounds
   (`reduce.gp`).
5. Direct check of m ≤ 60 (and, as a cross-check, m ≤ 5000 by `direct.gp`) gives the 7 solutions.

**Evidence.**
- Lean + Mathlib: [`A217396_mathlib.lean`](A217396_mathlib.lean). Main theorem
  `A217396.A217396_main`: assuming `RN` (Nagell's theorem) and `TetBound`
  (y^3 − y + 8 = 2^m ⇒ m ≤ 50), for every k ≥ 1, (2^k − 2 = n(n+1) for some n) ∨
  (2(2^k − 2) = 3·Te_j for some j) ↔ k ∈ {1, 2, 3, 5, 7, 13}. The translations to the two
  equations, the witnesses and the exclusion of all k ≤ 48 for (b) (bracketing j between
  consecutive values of j(j+1)(j+2)) are checked. Axioms: propext, Classical.choice, Quot.sound.
- `certificate/`: PARI/GP 2.15 scripts and outputs (`s1`, `dep`, `baker`, `reduce`, `direct`);
  each run with `gp -q -D recover=0`, exit code 0, no `***`.
- Outside Lean: Nagell's theorem; `TetBound` (Matveev's theorem as stated in Bugeaud–Mignotte–
  Siksek, Ann. Math. 163 (2006), Thm 9.4; the Dujella–Pethő lemma; the PARI computations of the
  field data, heights and continued fractions at 400 digits).

**Review level.** `lean-witness` (translation and finite part in Lean; the Baker bound and its
reduction are computed and re-derived here, not formalised).

**Prior art.** Searched 2026-11-06: OEIS A217396 (current entry and history), A217482, A076046;
web search for y^3 − y + 8 = 2^n and for tetrahedral analogues of Ramanujan–Nagell (none found;
the Physics Forums thread only reports the search to 1.41·10^1505); google-deepmind/
formal-conjectures (HEAD 2026-11-05) and otoi-lab/oeis-lean-proofs (HEAD 2026-10-13), no entry.
Part (a) is Nagell's theorem; part (b) is new as far as found (the scan's earlier attempt on
A217482 stalled before the Baker step).

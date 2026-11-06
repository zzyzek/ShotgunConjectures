# OEIS A072939: c(k) → ∞ exactly when n − 1 has odd 2-adic valuation, so a(n) = A036554(n) + 1

**Source.** OEIS [A072939](https://oeis.org/A072939) (B. Cloitre, 2002): c(1) = 1, c(2) = n,
c(k+2) = (c(k+1) + c(k))/2 if c(k+1), c(k) have the same parity, otherwise |c(k+1) − 2c(k)|; the sequence lists
the n with lim c(k) = ∞. Comment: "Conjecture: a(n) = A036554(n)+1." (V. Jovovic, Apr 01 2003). A036554 lists
the numbers whose binary expansion ends in an odd number of zeros. (OEIS text, CC BY-SA 4.0, revision #32 of
Apr 22 2025; a later comment by R. Stephan states the formula without proof.)

**Reading.** n ranges over n ≥ 1 (the listed terms; n = 0 also diverges: 1, 0, 2, 1, 3, 2, ...).

**Result.** True: for n ≥ 1, c(k) → ∞ iff n − 1 = 2^v·u with u odd and v odd. Hence a(n) = A036554(n) + 1, and
the entry's m(n) is u, the odd part of n − 1. Otherwise c(k) is eventually 1.

**Argument.** Work with pairs (c(k), c(k+1)). Write up(a, E) = (a, a+E) and down(b, E) = (b+E, b).
1. *Halving.* up(a, 2D) ↦ (a+2D, a+D) = down(a+D, D) and down(a, 2D) ↦ (a, a+D) = up(a, D) (same parity:
   average). From (1, n) = up(1, 2^v u), after v steps the pair is up(1+cu, u) for v even or down(1+cu, u) for v
   odd, for some c ≥ 0 (every move adds a multiple of u).
2. *Odd gap, descending.* For odd m: down(b, m) = (b+m, b) ↦ (b, b+2m) ↦ (b+2m, b+m) = down(b+m, m). So
   c grows by m every two steps and tends to ∞.
3. *Odd gap, ascending.* For odd u, two steps take up(x, u) to up(x−u, u) if x > u, and up(x, u) to
   up(u−x, x) if x ≤ u. From up(1+cu, u): c subtractions reach up(1, u), then up(u−1, 1), then
   up(x, 1) ↦ up(x−1, 1) down to up(0, 1) = (0, 1) ↦ (1, 1), which is fixed. So c(k) is eventually 1.
4. n = 1 is the fixed pair (1, 1). For n ≥ 2 write n − 1 = 2^v u; steps 1–3 decide by the parity of v.

**Evidence.**
- Lean (core): [`A072939.lean`](A072939.lean). `A072939_c n k` = c(k+1) by iterating the pair map;
  `A072939_diverges n` := ∀ M, ∃ K, ∀ k ≥ K, M ≤ c. Main theorem `A072939_main`: for n ≥ 1,
  `A072939_diverges n ↔ ∃ j u, n = 2^(2j+1)·(2u+1) + 1`. Lemmas `A072939_halve` (step 1),
  `A072939_down_iter`, `A072939_div_of_down` (step 2), `A072939_gap1`, `A072939_asc`,
  `A072939_not_div_of_fix` (step 3). `A072939_data`: the first 20 data terms by `decide`.
  Axioms: propext, Quot.sound.
- [`certificate/check.py`](certificate/check.py): the classification agrees with the dynamics for n < 20000.
- Outside Lean: that `A072939_step` transcribes the rule (|b − 2a| by cases), and the step from the set
  equality to the index equality of the two increasing listings.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: OEIS A072939, A036554, A079523 entries; web search. No proof found (the
entry's comments describe the eventual pattern from examples only). Not in google-deepmind/formal-conjectures
or otoi-lab/oeis-lean-proofs (local clones).

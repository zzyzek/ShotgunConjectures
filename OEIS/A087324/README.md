# OEIS A087324: no term has a perfect-square prime signature

**Source.** [A087324](https://oeis.org/A087324) (n such that n and its 9's complement have the same prime
signature), comment: "Conjecture: (1) Sequence is infinite. (2) For every prime signature there corresponds a
term in this sequence." (OEIS text, CC BY-SA 4.0.)

**Reading.** The 9's complement of a d-digit n is 10^d − 1 − n.

**Result.** Conjecture (2) is false: no term has an all-even signature such as p^2 or p^2·q^2.
Conjecture (1) is not addressed (open).

**Argument.** A number has an all-even signature iff it is a perfect square. If n and its complement
share such a signature, both are squares, but they sum to 10^d − 1 ≡ 3 (mod 4) for d ≥ 2, while squares
are 0 or 1 mod 4. For d = 1 the pairs (n, 9 − n) contain no two squares. (The 10's-complement analogue,
A087325, is refuted in its entry in the same way.)

**Evidence.**
- Lean: [`A087324.lean`](A087324.lean): x^2 mod 4 ∈ {0, 1}; x^2 + y^2 ≠ 10^d − 1 for d ≥ 2; the d = 1 pairs.
  Outside Lean: "same all-even signature ⇒ both squares".
- `certificate/check.py`: terms below 10^5, none a square.
- Lean (Mathlib): [`A087324_mathlib.lean`](A087324_mathlib.lean), `A087324_main`: with prime signature = multiset of exponents of `Nat.factorization` and the 9's complement 10^d - 1 - n (d = number of digits), no n ≥ 1 with equal signatures has a nonempty all-even signature; signature {2} (that of 4) has no term. The step "all-even signature ⇒ square" is proved there; nothing outside Lean.

**Review level.** `lean-proof` for conjecture (2) false (Mathlib file above); conjecture (1) not addressed.
**Prior art.** Partly known: the same idea refutes conjecture (2) of the 10's-complement analogue in [A087325](https://oeis.org/A087325); [A087324](https://oeis.org/A087324) still has it open. Conjecture (1) not addressed. Searched OEIS entries, references and history, web. Checked 2026-11-04.

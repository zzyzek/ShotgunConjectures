# OEIS A094358: Munafo's conjecture is equivalent to "all Fermat numbers are squarefree"

**Source.** [A094358](https://oeis.org/A094358), "Squarefree products of factors of Fermat numbers". Comment:
"Conjectured (by Munafo, see link) to be the same as: numbers n such that 2^^n == 1 mod n, where 2^^n is
A014221(n)." The entry adds that one inclusion follows from Alekseyev's observations and the CRT, and that "the
converse is true iff all Fermat numbers are squarefree". (OEIS text, CC BY-SA 4.0, revision #66, checked
2026-11-06.)

**Result.** Not settled. Proved (in Lean): (1) every term of A094358 satisfies 2^^n == 1 (mod n); (2) Munafo's
conjecture holds if and only if every Fermat number is squarefree, an open problem. The equivalence is the one
asserted in the entry; the proof here is complete.

**Argument.**
1. For n >= 2, 2^^n = 2^(2^(2^^(n-2))), so 2^^n == 1 (mod n) gives n | 2^(2^j) - 1 with j = 2^^(n-2). Conversely,
   if n | 2^(2^j) - 1 then n is odd, the order of 2 mod n divides 2^j, so it is 2^i with 2^i <= phi(n) < n, so
   i < n <= 2^^(n-2) + 1, and 2^i divides 2^^(n-1) = 2^(2^^(n-2)); hence 2^^n == 1 (mod n).
2. 2^(2^j) - 1 = F_0 F_1 ... F_(j-1), and Fermat numbers are pairwise coprime (Mathlib).
3. A term of A094358 is the product of its distinct primes, each dividing some F_k; it divides F_0 ... F_(J-1) for
   J large, so (1) applies.
4. If all F_k are squarefree, every divisor of F_0 ... F_(j-1) is squarefree and its primes divide some F_k, so
   the two sets agree. If p^2 | F_k for a prime p, then n = p^2 divides 2^(2^(k+1)) - 1, so 2^^n == 1 (mod n),
   but p^2 is not squarefree: the sets differ.

**Evidence.**
- Lean (Mathlib): [`A094358_mathlib.lean`](A094358_mathlib.lean). `tow` is 2^^k; `InSeq n` = n squarefree and
  every prime factor divides some `Nat.fermatNumber k`. Theorems `A094358.munafo_iff`,
  `A094358.A094358_subset_munafo`, `A094358.munafo_conjecture_iff : (∀ n, 1 ≤ n → (InSeq n ↔ tow n ≡ 1 [MOD n]))
  ↔ ∀ k, Squarefree (Nat.fermatNumber k)`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at
  most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py) ([`check.out`](certificate/check.out)): the two sets agree for
  small n (both computed through the order criterion of step 1).
- Outside Lean: none for the equivalence. The squarefreeness of Fermat numbers is open (known only for small k).

**Review level.** `lean-proof` (of the equivalence; the conjecture itself is open).

**Prior art.** Checked 2026-11-06. The equivalence is stated in the entry (comment after Alekseyev's
observation) and by J. S. Nielsen's characterisation by the order of 2. Ghosh-Jain (2021, ResearchGate) discuss
the conjecture; not retrievable. Whether all Fermat numbers are squarefree is a well-known open question (Guy,
UPINT A3). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.

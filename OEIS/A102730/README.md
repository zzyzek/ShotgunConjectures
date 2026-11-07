# OEIS A102730: the number of factorials inside the binary expansion of n! is unbounded

**Source.** [A102730](https://oeis.org/A102730), number of factorials contained in the binary representation
of n!. Comment: "Conjecture: the sequence is bounded." C. R. Greathouse IV (Aug 21 2011): "I conjecture the
contrary: for every k, there exists n with a(n) > k. See A103670." (entry checked 2026-11-07).

**Reading.** a(n) = #{k : 0 <= k <= n, the binary word of k! is a contiguous substring of the binary word of n!}
(0! and 1! both count, as in the entry's example a(6) = 5). This reproduces a(0..104) of the entry
(certificate/check.py).

**Result.** The conjecture is false: a(n) is unbounded (Greathouse's opposite conjecture is true). More
precisely, for every m there are infinitely many n > m with a(n) >= a(m) + 1.

**Argument.** Write odd(x) for the odd part of x and s(x) = odd(x!) mod 2^L, for a fixed L >= 3.

1. *Substrings.* bin(x!) is bin(odd(x!)) followed by v_2(x!) zeros. If odd(n!) ≡ odd(m!) (mod 2^L) with
   L >= bitlength(odd(m!)) and n >= m, then bin(n!) ends with bin(odd(m!)) followed by v_2(n!) >= v_2(m!)
   zeros, so bin(m!) is a substring of bin(n!). Substrings of substrings are substrings, so every k counted
   by a(m) is counted by a(n), and n itself is counted too: a(n) >= a(m) + 1.
2. *Products of odd numbers.* odd(x!) = prod_{j >= 0} P(floor(x/2^j)), where P(y) is the product of the odd
   numbers <= y. The odd residues mod 2^L form a group whose elements of order <= 2 are ±1, 2^(L-1) ± 1, so
   their product is ≡ 1 (mod 2^L); hence P(y) ≡ 1 when 2^L | y + 1 or 2^L | y, more generally P depends only on
   y mod 2^L.
3. *Lemma A.* If r < 2^(N-L+1) then s(2^N a + r) ≡ s(2^N a) s(r). Indeed, for 1 <= i <= r,
   v_2(i) <= N - L, so odd(2^N a + i) = 2^(N - v_2(i)) a + odd(i) ≡ odd(i) (mod 2^L).
4. *Lemma B.* If 2^L | a then s(2^N a) ≡ s(a). Indeed odd((2^N a)!) = odd(a!) prod_{k=1}^{N} P(2^k a), and
   each P(2^k a) is a product over whole periods of the odd residues mod 2^L, so ≡ 1.
5. *Closure.* Let S = {s(a) : a >= 1, 2^L | a}. For s(a), s(b) in S pick N with 2^(N-L+1) > b; then
   2^N a + b is a multiple of 2^L and s(2^N a + b) ≡ s(2^N a) s(b) ≡ s(a) s(b) by A and B. So S is a nonempty
   multiplicatively closed subset of the finite group (Z/2^L)^*, hence a subgroup, and 1 ∈ S. Explicitly
   a = 2^L (1 + 2^T + 2^(2T) + ... + 2^((J-1)T)) with J = 2^(L-2) and T large gives s(a) ≡ s(2^L)^J ≡ 1.
6. *Conclusion.* Given m, take L = max(3, bitlength(odd(m!))), a with 2^L | a and s(a) ≡ 1, and N with
   2^(N-L+1) > m. For n = 2^N a + m, Lemma A and B give s(n) ≡ s(a) s(m) ≡ s(m), and step 1 gives
   a(n) >= a(m) + 1. Iterating from m = 0 gives n with a(n) >= K for every K.

The n produced are huge (for m = 7, n has 1800 bits); the argument says nothing about A103670 (the least m
with a(m) = n) beyond its existence.

**Evidence.**
- [`certificate/check.py`](certificate/check.py): reproduces a(0..104); checks s(x) against odd(x!) mod 2^L
  for x <= 400, Lemma A and Lemma B on ranges, the explicit a of step 5 for L = 3..10, and the construction
  of step 6 for m = 3..8 (s(n) ≡ odd(m!) mod 2^L).
- Lean (Mathlib): [`A102730_mathlib.lean`](A102730_mathlib.lean): `A102730_unbounded` (∀ K, ∃ n, K ≤ a n) and
  `A102730_step` (∀ m, ∃ n, m < n ∧ a m + 1 ≤ a n), with `a n` the number of k ≤ n such that `Nat.digits 2 k!`
  is an infix of `Nat.digits 2 n!`. The Lean route replaces steps 4-5 by pigeonhole: among the spaced sums
  B_k = sum_{j<k} 2^(N + jD), two have the same odd(B!) mod 2^L, and Lemma A then gives odd((2^M A)!) ≡ 1
  (`lemmaA`, `Bseq_split`, `core`); `digits_fact` and `infix_of_modEq` are step 1. Checked with
  `tools/leancheck-mathlib.sh` (rechecked independently), no warnings, axioms propext, Classical.choice,
  Quot.sound.
- Outside Lean: none. Not verified in Lean: agreement with the listed terms (check.py, a(0..104)).

**Review level.** `lean-proof`.

**Prior art.** OEIS A102730, A103670, A103671, A103672 (Greathouse's conjecture of unboundedness, no proof),
google-deepmind/formal-conjectures (no file for A102730), otoi-lab/oeis-lean-proofs (none); 2026-11-07.
The argument (2-adic behaviour of odd parts of factorials, as in Morita's p-adic Gamma function) is ours.

# OEIS A165300: Layman's four rules for the 1,2-path sequence

**Source.** OEIS [A165300](https://oeis.org/A165300) (offset 1): "a(n) is the smallest number not already
present that permits the cyclic repetition of the path 1,2 of the digits in the sequence": 1, 2, 12, 121, 21,
212, 1212, ... Conjecture (J. W. Layman, Sep 2009): (1) for n > 1, if a(n) begins and ends with 1, a(n+1) is
a(n) with the initial 1 deleted; (2) begins with 1, ends with 2: append a final 1; (3) begins with 2, ends
with 1: append a final 2; (4) begins and ends with 2: prepend a 1. "confirmed through a(140) ... (and
should be fairly easy to prove)". (OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05, revision #12.)

**Reading.** a(n) is the least m > 0, not among a(1), ..., a(n−1), such that the decimal digits of
a(1), ..., a(n−1), m written one after another read 1, 2, 1, 2, ... This reproduces the 25 printed terms
(also by brute force over all integers for the first 12).

**Result.** True (all four rules, for every n; the closed form below is also proved).

**Argument.** If the digits so far have length L, the admissible m are exactly the alternating numbers
(digits 1212... or 2121...) whose first digit is the (L+1)-st digit of the pattern; among these a longer one
is larger, so a(n) is the shortest unused one. Induction on j: after a(4j+2) the used numbers are exactly
the alternating numbers with at most 2j+1 digits (both starting digits), and L = (2j+1)(2j+2) is even.
Then a(4j+3) = 1212...12 (2j+2 digits), a(4j+4) = 1212...121 (2j+3), a(4j+5) = 2121...21 (2j+2),
a(4j+6) = 2121...212 (2j+3), and the invariant holds for j+1. With a(1) = 1, a(2) = 2 the rules read off
directly: 1...2 (even length, start 1) → append 1; 1...1 (odd, start 1) → delete the first digit;
2...1 → append 2; 2...2 → prepend 1 (including a(2) = 2 → a(3) = 12). Rule (1) fails at n = 1
(deleting the 1 of a(1) = 1 leaves nothing), which is why the entry excludes it.

**Evidence.**
- Lean (Mathlib): [`A165300_mathlib.lean`](A165300_mathlib.lean). The sequence is defined by the entry's name
  (`A165300_adm`, `A165300_next` = Nat.find of the least admissible m, `A165300_terms`, `A165300_a`); digits
  are Mathlib `Nat.digits 10`, reversed. `A165300_rule1` (n > 1), `A165300_rule2`, `A165300_rule3`,
  `A165300_rule4` (n ≥ 1) state the four rules on the digit lists of a(n) and a(n+1) (first digit =
  `head?`, last = `getLast?`). `A165300_closed`: a(n) = `A165300_cf n` (closed form above);
  `A165300_next_eq` (the next term is the shortest unused alternating number); `A165300_state` (the
  invariant); `A165300_data` (25 printed terms, `decide` on the closed form).
  Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: the definition simulated (shortcut and plain brute force), the 25 printed terms,
  the four rules and the closed form for n < 300.
- Outside Lean: nothing.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: the entry has the conjecture and P. P. Lava's formula for a(n+1) in terms of
a(n) and n mod 4 (equivalent to the rules, unproved); no proof linked. A web search found nothing; not in
google-deepmind/formal-conjectures.

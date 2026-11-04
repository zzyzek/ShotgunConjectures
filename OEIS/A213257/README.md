# OEIS A213257: the excluded integers are the positions of 2 in a morphic word

**Source.** OEIS [A213257](https://oeis.org/A213257): a(1) = 1, a(2) = 2 and a(n) the least integer > a(n-1) such that no three terms form a progression {x, 2x, 4x}. Conjecture: "The positive integers that are not in this sequence are given by the positions of 2 in the fixed-point of the morphism 0->01, 1->02, 2->03, 3->01 (see A191255)." (C. Kimberling, 2012; OEIS text, CC BY-SA 4.0.)

**Result.** True: n is excluded from A213257 iff v_2(n) ≡ 2 (mod 3), iff the fixed point has
letter 2 at position n.

**Argument.**
- Greedy set. A progression x, 2x, 4x lies inside one chain {o·2^e : e ≥ 0} (o odd). When n = o·2^e
  is considered, the larger members of its chain are not yet decided, so n is rejected iff o·2^(e-1)
  and o·2^(e-2) are both in the set. Hence membership depends only on e: e = 0, 1 in; e = 2 out;
  e = 3 in (e - 1 = 2 is out); e = 4 in; e = 5 out; ... so n is out iff e ≡ 2 (mod 3).
  (a(1) = 1, a(2) = 2 agree with this rule.)
- Morphism. The morphism is 2-uniform with every image starting with 0, so the fixed point w
  (positions from 1) has w(2m - 1) = 0 and w(2m) = g(w(m)) with g: 0→1, 1→2, 2→3, 3→1. So
  w(n) = g^(v_2(n))(0): 0, 1, 2, 3, 1, 2, 3, ... for v_2(n) = 0, 1, 2, ..., and w(n) = 2 iff
  v_2(n) ≡ 2 (mod 3), v_2(n) ≥ 2.

**Evidence.**
- `certificate/a213257.py`: greedy set, the v_2 rule and the morphic word agree for n ≤ 2·10^5.
- Lean: not done.

**Review level.** `rechecked`.

**Prior art.** The entry A213258 (fetched 2026-11-01) states both conjectures are correct, n =
2^(3t+2)·(odd) (J. Song, Sep 2018), and gives density 1/7 (A. Eldar). So resolved by others.

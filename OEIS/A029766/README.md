# OEIS A029766: a(n) = n!·A040039(n−1) holds on the data; the entry's name does not determine the sequence

**Source.** OEIS [A029766](https://oeis.org/A029766) (offset 0): "Unary-binary rooted trees with n nodes":
0, 1, 2, 12, 48, 360, 2160, 25200, ... (20 terms, a(0..19); reference Bergeron–Labelle–Leroux,
*Combinatorial Species and Tree-Like Structures*, p. 254). Conjecture (V. Kotesovec, Sep 2013): "for n > 0,
a(n) = n! * A040039(n-1)." The e.g.f. once printed in the entry is marked incorrect (it is the o.g.f. of
Motzkin numbers). (OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05, revision #18.)

**Reading.** The name does not fix the data. Labelled rooted trees with every node of out-degree ≤ 2 give
1, 2, 9, 60, ... (A036774; differs at n = 3); with ordered (plane) children n!·Motzkin(n−1) = 1, 2, 12, 96, ...
(differs at n = 4). The book page was not available here, so which table column the data come from is not
known. One family matches all 19 terms: n! times the number u(n) of unlabelled unary-binary trees in which
the two branches of every binary node are equal (equivalently, such trees with labelled nodes and ordered
branches; these have no automorphisms, so each shape has n! labellings). A040039 is used as defined in its
entry: first differences of A033485 (A033485(1) = 1, A033485(n) = A033485(n−1) + A033485(⌊n/2⌋)).

**Result.** Partial. On the listed data the conjecture holds (n = 1..19). For all n it holds for the reading
above: u(n) = A040039(n−1). Whether that is the sequence the entry intends is not settled.

**Argument.** A tree of this kind with n ≥ 2 nodes is either a unary root over such a tree with n − 1
nodes, or (n odd) a binary root over two copies of such a tree with (n − 1)/2 nodes. So u(1) = 1,
u(n) = u(n−1) + [n odd]·u((n−1)/2). The sequence D(n) = A033485(⌊(n+1)/2⌋) satisfies the same recurrence
(for n = 2m+1, A033485(m+1) = A033485(m) + A033485(⌊(m+1)/2⌋)), and D(n) = A033485(n+1) − A033485(n) =
A040039(n−1) by the A033485 recurrence. (The entry of A040039 already lists this recurrence, attributed to
G. Wiseman, "using offset 1".)

**Evidence.**
- Lean (Mathlib): [`A029766_mathlib.lean`](A029766_mathlib.lean). `A029766_data`: n!·A040039(n−1) for
  n = 1..19 equals the printed a(1..19) (`decide`). `A029766_main (n) (hn : 1 ≤ n)`:
  `Set.ncard {t : A029766_T | size t = n ∧ sym t} = A040039 (n - 1)`, with `A029766_T` the inductive type of
  unary-binary trees (`leaf`, `un`, `bin`) and `sym` requiring equal branches at binary nodes.
  Supporting: `A029766_mem_gen`, `A029766_nodup_gen` (an explicit duplicate-free list of the trees),
  `A029766_length_gen`, `A033485_rec`, `A040039_data` (26 printed terms of A040039).
  Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: the printed terms against the three readings (first mismatch n = 3 for labelled
  unordered trees, n = 4 for labelled plane trees; the equal-branch family matches all 19), and
  a(n) = n!·A040039(n−1) for n = 1..19.
- Outside Lean: the choice of reading. The labelled-plane interpretation of n!·u(n) is stated, not formalized
  (only u(n) is counted in Lean).

**Review level.** `lean-proof` for the two Lean statements; `agent` for the reading.

**Prior art.** Checked 2026-11-05: the entry gives no definition beyond the name and the book reference; a web
search found no discussion of the mismatch; not in google-deepmind/formal-conjectures. The u-recurrence is
the A040039 formula of G. Wiseman (Oct 2018), so the all-n statement under this reading is close to known.

# BMP 9.6 Conjecture 3 (Karzanov-Lomonosov): k-cross-free families are linear in n; the O(kn) form is still open

**Source.** Brass-Moser-Pach, Research Problems in Discrete Geometry (2005), Section 9.6,
Conjecture 3 (paraphrased): a family of subsets of an n-set with no k pairwise crossing
members has at most Ckn members, C an absolute constant. Two sets cross when all four Venn
regions (A\B, B\A, A∩B, X\(A∪B)) are nonempty.

**Reading.** The conjecture has two strengths: linear in n for each fixed k (|F| <= c_k n), and
the stated form c_k = O(k).

**Result.** Partial, known. Linearity for each fixed k holds:
- E. Knill, Families of sets with locally bounded width, Graphs and Combinatorics 10 (1994)
  145-157, proves that k-wise laminar families (no antichain of k members with a common point)
  have size O_k(n); a k-cross-free family contains a k-wise laminar subfamily of at least half
  its size (Tomon, Lemma 2.1), so |F| <= c_k n.
- I. Tomon, Cross-free families have linear size, arXiv:2603.05443 (v3, Sep 2026), gives an
  independent proof (Theorem 1.1) and records that Knill's 1994 paper had been overlooked.
The constant in Tomon's proof is huge (an induction on k with trees of branching about
h/(2k)^{k^2}); neither paper gives c_k = O(k). The Ckn form stays open; known exact cases
are k = 2 (4n - 2, Edmonds-Giles) and k = 3 (8n - 20, Dress-Koolen-Moulton 2005).

**Argument.** Citation only.

**Evidence.** Tomon arXiv:2603.05443v3, abstract, update note, Theorem 3.1 and its proof, read
2026-11-06. No Lean. Outside Lean: everything.

**Review level.** `agent`.

**Prior art.** Searched 2026-11-06: arXiv 2603.05443 (full text), web,
google-deepmind/formal-conjectures HEAD 2026-11-06 (no Karzanov-Lomonosov entry).

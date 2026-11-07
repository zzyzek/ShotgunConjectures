# AMR froberg-R: explicit odd-degree forms with the Lundqvist–Nicklasson series (partial)

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and from the
other pockets*, Arnold Math. J. 4 (2018), Section 4.4, Problem R, listed via
https://amathr.org/problems/. Paraphrase: for each n and odd d, find an explicit form f of degree d
in the exterior algebra E on n generators such that E/(f) has the minimal series given by
Lundqvist–Nicklasson (S. Lundqvist, L. Nicklasson, *On generic principal ideals in the exterior
algebra*, arXiv:1803.03563, "LN", Corollary 3.2: a lower bound a = b + c, in lexicographic order,
for HS(E/(f)) for every odd form f).

**Reading.** "Minimal series" = the LN bound a. It is not attained at (n, d) = (9, 3) (LN Prop. 4.4),
which is excluded. LN already give explicit forms for d = n − 2 and for d = n − 3, n even, and say
that they found none for d = n − 4.

**Result (partial).**
1. Certification principle. For an integer form f, rank over Q ≥ rank mod p gives HS_Q(f) ≤ HS_p(f)
   coefficientwise, while HS_Q(f) ⪰_lex a by LN Cor. 3.2. So HS_p(f) = a for one prime p implies
   HS_Q(f) = a, and then a is also the generic (minimal) series for that (n, d).
2. d = n − 4, n odd (new reduction). HS(E/(f)) = a iff the symmetric bilinear form
   B_f(α, β) = [α ∧ β ∧ f] on E_2 is nondegenerate. (Degrees below n − 4 are free; degree n − 4 needs
   f ≠ 0; degrees n − 2, n − 3, n − 1, n need rank B_f = C(n,2), injectivity of ·f on E_1,
   surjectivity of ·f: E_3 → E_{n−1} and f ≠ 0; nondegeneracy of B_f implies injectivity on E_1, since
   x·f = 0 gives B_f(x∧y, ·) = 0, and LN Prop. 2.2 turns injectivity on E_1 into surjectivity on E_3.
   The LN bound in these degrees is C(n,4) − 1, C(n,3) − n, 0, 0, 0, checked against the formula.)
3. Explicit family for d = n − 4: f_n = Σ_{|S|=4} (max S − min S)·sgn(S, S^c)·e_{S^c} (the Hodge dual
   of η = Σ_S (max S − min S) e_S). Then B_f[P, Q] = ±(max(P∪Q) − min(P∪Q)) for disjoint pairs P, Q
   (sign: − for crossing pairs). This matrix has full rank mod 1000003 for every odd n, 7 ≤ n ≤ 23,
   so E/(f_n) has the LN series for d = n − 4, n = 7, 9, …, 23 (n = 7 is d = 3). A proof of
   nondegeneracy for all odd n is open (the determinants have no visible pattern:
   432, −219948493824, … for n = 7, 9).
4. Sparse cyclic forms for all small cases: for every odd d with 3 ≤ d ≤ n − 2 and 5 ≤ n ≤ 13,
   (n, d) ≠ (9, 3), the orbit sum of one or two "seed" d-subsets under the rotation i ↦ i + 1 mod n
   (coefficients 0, ±1) attains a; table in certificate/seeds_table.out (e.g. d = 3:
   Σ_i x_i x_{i+1} x_{i+2} for n ≤ 10, Σ_i x_i x_{i+1} x_{i+3} for 6 ≤ n ≤ 14, n ≠ 9; the latter fails at
   n = 15).
5. Consequence for LN Question 6.1 (is a the minimal series for (n, d) ≠ (9, 3)?): yes in the new cases
   (n, d) = (12, 7), (13, 7), (13, 9), (15, 11), (17, 13), (19, 15), (21, 17), (23, 19), beyond LN
   Prop. 4.5 (d = 3, n ≤ 17; d = 5, n ≤ 13; d = 7, n ≤ 11) and LN Props. 4.1–4.2 (d = n − 2, n − 3).

**Evidence.** certificate/hs.py (LN bound and Hilbert series mod 1000003), seeds.py and
seeds_table.out (cyclic forms, every degree checked), span.py (full series of f_n for n = 7, 9, 11, 13,
equal to a), spanrank.py and span_rank.out (rank of B_f for odd n ≤ 23), fam.py and fam14.out
(Σ x_i x_{i+1} x_{i+3} for n = 14, 15). No Lean file. Outside Lean: everything (the reduction in item 2
is a hand proof; ranks are computed mod p in Python).

**Review level.** `agent`.

**Prior art.** LN (2018/2019): explicit forms for d = n − 2, d = n − 3 (n even), (9, 3); minimal series
by Macaulay2 for the ranges in item 5; Remark 4.3 there says no form was found for d = n − 4. Searched
2026-11-07: web search; google-deepmind/formal-conjectures (no entry). No later work on Problem R found.

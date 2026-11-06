# OEIS A007413: counts of 1's between consecutive 2's of A076826

**Source.** [A007413](https://oeis.org/A007413): "A squarefree (or Thue-Morse) ternary sequence: closed under
1->123, 2->13, 3->2. Start with 1." Comment: "Conjecture. The sequence is formed by the numbers of 1's between every
pair of consecutive 2's in A076826. - _Vladimir Shevelev_, May 31 2009". [A076826](https://oeis.org/A076826):
a(n) = 2*(Sum_{k=0..n} A010060(k)) - n. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** A007413 has offset 1 and is the fixed point of sigma: 1 -> 123, 2 -> 13, 3 -> 2 starting with 1.
A076826 has offset 0. The claim: for n >= 1, A007413(n) is the number of i with p_n < i < p_{n+1} and
A076826(i) = 1, where p_1 < p_2 < ... are the positions of the 2's.

**Result.** True: with t = Thue-Morse (A010060), A007413(n+1) = 2 + t(n) - t(n+1), and A007413(n) is the number of 1's
of A076826 between its n-th and (n+1)-th 2 for every n >= 1.

**Argument.**
1. *Fixed point.* Let u(n) = 2 + t(n) - t(n+1) (n >= 0). From t(2m) = t(m), t(2m+1) = 1 - t(m):
   u(2m) = 1 + 2t(m), u(2m+1) = 3 - t(m) - t(m+1). Put L(m) = 2m + t(m). Checking the four values of
   (t(m), t(m+1)) gives sigma(u(m)) = u(L(m)) ... u(L(m+1) - 1), so sigma maps the prefix of u of length m onto
   the prefix of length L(m). Since u(0) = 1, sigma^k(1) is the prefix of u of length l_k with l_0 = 1,
   l_{k+1} = L(l_k) >= k + 2. So A007413(n+1) = u(n).
2. *A076826.* Pairs (2j, 2j+1) contain one odious number each, so Sum_{k<2m} t(k) = m. Hence A076826(2m) = 2t(m),
   A076826(2m+1) = 1 (Cloitre's formula in the entry). The 2's are at 2x with t(x) = 1, i.e. at 2o(j), where
   o(j) = 2j + 1 - t(j) is the j-th odious number (j >= 0); the 1's are at the odd positions.
3. Between 2o(n-1) and 2o(n) there are o(n) - o(n-1) = 2 + t(n-1) - t(n) = u(n-1) = A007413(n) odd positions.

**Evidence.**
- Lean (Mathlib): [`A007413_mathlib.lean`](A007413_mathlib.lean) (namespace `A007413Proof`). `tm n` is the parity
  of the binary digit sum, `sig` the morphism on lists, `A007413 n = (sig^[n] [1])[n-1]`, `A076826 n =
  2 Σ_{k ≤ n} tm k - n` over ℤ, `two n = Nat.nth (· is a 2 of A076826) (n-1)`. Main theorem `A007413_main :
  1 ≤ n → A007413 n = #{i ∈ (two n, two (n+1)) | A076826 i = 1}`. Also `A007413_iter` (every iterate sig^[k] [1]
  agrees with u at each position) and `len_iter` (sig^[k] [1] has more than k letters), so `A007413` is the
  fixed point. Route: `s_u`, `flat_prefix`, `iter_eq`, `A007413_eq`; `sum_pairs`, `b_even`, `b_odd`, `two_eq`,
  `count_odd`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): the morphism against the b-file
  ([`certificate/b007413.txt`](certificate/b007413.txt), 10000 terms), A076826 against its b-file
  ([`certificate/b076826.txt`](certificate/b076826.txt)), and the claim for n < 150000.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The statement follows at once from published facts: A001969 (evil numbers)
records the theorem "first differences give A036585", observed by Franklin T. Adams-Watters and proved by Max
Alekseyev (2006, proof in the entry, via e(n) = 2n + t(n)); A036585 is A007413 with letters 1 and 3 swapped
(A007413(n) = 4 - A036585(n-1), Deléham), and odious gaps are 4 minus evil gaps; A076826(2n) = 2A010060(n),
A076826(2n+1) = 1 is Cloitre's formula there. A036577 has the companion statement "Number of 1's between
successive 0's in A010060" (Berstel's equivalences). No combined write-up of Shevelev's form was found. Not in
google-deepmind/formal-conjectures (no file for 007413) or otoi-lab/oeis-lean-proofs.

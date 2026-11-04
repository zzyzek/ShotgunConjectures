import OpenProblemsLib

/-
NT-B2.7 (Mathlib). Guy B2 (Cohen–Sorli, Goto–Shibata): n is harmonic if H(n) = n·d(n)/σ(n)
is an integer; a harmonic number m > 1 is a seed if no unitary divisor e of m with 1 < e < m
is harmonic. Does every harmonic number have a unique harmonic seed?
README reading: a seed of n is a harmonic seed that is a unitary divisor of n (d ∣ n,
gcd(d, n/d) = 1); 1 is excluded. README result: no; n = 2⁴·3·5²·7²·19·31²·83·331 =
29495815011600 (H = 525) has the two seeds m₁ = n/5² = 1179832600464 (H = 217) and
m₂ = n/3 = 9831938337200 (H = 350).

Main theorem `B2_7_main`: n is harmonic with H(n) = 525; m₁ and m₂ are seeds (`IsSeed`),
unitary divisors of n, with H = 217 and 350, and m₁ ≠ m₂. `B2_7_false`: the uniqueness
question has a negative answer. σ = Mathlib `ArithmeticFunction.sigma 1`, d(n) =
`n.divisors.card`. Proof: σ and d by multiplicativity from the factorizations; every unitary
divisor of val f is val s for a sublist s of f (`OpenProblemsLib.ArithFactor.unitary_val`), and
the 2⁷ sublists of the factor lists of m₁ and m₂ are checked by the kernel.

Outside Lean: nothing.
-/

open OpenProblemsLib.ArithFactor ArithmeticFunction

def Harmonic (n : ℕ) : Prop := 0 < n ∧ sigma 1 n ∣ n * n.divisors.card

/-- H(n) = n·d(n)/σ(n). -/
def Hm (n : ℕ) : ℕ := n * n.divisors.card / sigma 1 n

def UnitaryDivisor (d n : ℕ) : Prop := d ∣ n ∧ Nat.Coprime d (n / d)

/-- Cohen–Sorli seed: harmonic, > 1, and no harmonic unitary divisor strictly between 1 and m. -/
def IsSeed (m : ℕ) : Prop :=
  1 < m ∧ Harmonic m ∧ ∀ e, UnitaryDivisor e m → 1 < e → e < m → ¬ Harmonic e

def fn : PF := [(2, 4), (3, 1), (5, 2), (7, 2), (19, 1), (31, 2), (83, 1), (331, 1)]
def g1 : PF := [(2, 4), (3, 1), (7, 2), (19, 1), (31, 2), (83, 1), (331, 1)]
def g2 : PF := [(2, 4), (5, 2), (7, 2), (19, 1), (31, 2), (83, 1), (331, 1)]

theorem harm_of (f : PF) (n h : ℕ) (hf : factCheck f = true) (hn : val f = n)
    (hc : (0 < n && n * ndF f % sigF f == 0 && n * ndF f / sigF f == h) = true) :
    Harmonic n ∧ Hm n = h := by
  have hok := factOK_of_check f hf
  have hs : sigma 1 n = sigF f := by rw [← hn]; exact sigma_val f hok
  have hd : n.divisors.card = ndF f := by rw [← hn]; exact card_divisors_val f hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  refine ⟨⟨hc.1.1, ?_⟩, ?_⟩
  · rw [hs, hd]; exact Nat.dvd_of_mod_eq_zero hc.1.2
  · unfold Hm; rw [hs, hd]; exact hc.2

/-- Kernel check: every sublist s of f gives 1, val f, or a non-harmonic val s. -/
def seedCheck (f : PF) : Bool :=
  f.sublists.all (fun s => val s == 1 || val s == val f || val s * ndF s % sigF s != 0)

theorem seed_of (f : PF) (m h : ℕ) (hf : factCheck f = true) (hn : val f = m) (h1 : 1 < m)
    (hc : (0 < m && m * ndF f % sigF f == 0 && m * ndF f / sigF f == h) = true)
    (hs : seedCheck f = true) : IsSeed m ∧ Hm m = h := by
  obtain ⟨hh, hH⟩ := harm_of f m h hf hn hc
  refine ⟨⟨h1, hh, ?_⟩, hH⟩
  intro e ⟨hd, hu⟩ he1 hem ⟨_, he⟩
  have hok := factOK_of_check f hf
  rw [← hn] at hd hu
  obtain ⟨s, hsub, rfl⟩ := unitary_val f hok e hd hu
  have hoks := hok.sublist hsub
  rw [sigma_val s hoks, card_divisors_val s hoks] at he
  have := List.all_eq_true.mp hs s (List.mem_sublists.mpr hsub)
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  rcases this with (h' | h') | h'
  · omega
  · omega
  · exact h' (Nat.mod_eq_zero_of_dvd he)

theorem B2_7_main :
    Harmonic 29495815011600 ∧ Hm 29495815011600 = 525 ∧
      IsSeed 1179832600464 ∧ Hm 1179832600464 = 217 ∧
      IsSeed 9831938337200 ∧ Hm 9831938337200 = 350 ∧
      UnitaryDivisor 1179832600464 29495815011600 ∧
      UnitaryDivisor 9831938337200 29495815011600 ∧
      (1179832600464 : ℕ) ≠ 9831938337200 := by
  obtain ⟨a1, a2⟩ := harm_of fn 29495815011600 525 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨b1, b2⟩ := seed_of g1 1179832600464 217 (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  obtain ⟨c1, c2⟩ := seed_of g2 9831938337200 350 (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  refine ⟨a1, a2, b1, b2, c1, c2, ⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩, by norm_num⟩
  · unfold Nat.Coprime; decide +kernel
  · unfold Nat.Coprime; decide +kernel

/-- Seeds of n: seeds that are unitary divisors of n. -/
theorem B2_7_false :
    ¬ ∀ n : ℕ, Harmonic n → 1 < n → ∀ a b, IsSeed a → UnitaryDivisor a n →
      IsSeed b → UnitaryDivisor b n → a = b := by
  intro h
  obtain ⟨a1, -, b1, -, c1, -, d1, d2, hne⟩ := B2_7_main
  exact hne (h _ a1 (by norm_num) _ _ b1 d1 c1 d2)

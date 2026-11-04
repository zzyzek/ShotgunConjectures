import OpenProblemsLib

/-
NT-B2.8 (Mathlib). Guy B2 (Goto–Shibata): n is harmonic if H(n) = n·d(n)/σ(n) is an integer
and arithmetic if d(n) ∣ σ(n). Every harmonic n with H(n) = 3p < 300 (p prime) is arithmetic;
does this hold for all primes p? README result: no; n = 2⁸·7·19²·37·73·113·127 =
25075635936512 has H(n) = 339 = 3·113 and σ(n) ≡ 288 (mod d(n)); second example
n = 2⁸·5²·7·19·31·37·73·179 = 12757657068800, H(n) = 537 = 3·179, σ(n) ≡ 576 (mod d(n)).

Main theorem `B2_8_main`: for both n (σ = Mathlib `ArithmeticFunction.sigma 1`,
d(n) = `n.divisors.card`): n is harmonic, H(n) = 3p with p = 113 resp. 179 prime, and n is
not arithmetic, with the stated residues σ(n) mod d(n). `B2_8_false`: the question
"harmonic with H(n) = 3p, p prime ⇒ arithmetic" has a negative answer.
σ and d are computed from the factorizations by multiplicativity
(`OpenProblemsLib.ArithFactor.sigma_val`, `card_divisors_val`; primes by trial division).

Outside Lean: nothing.
-/

open OpenProblemsLib.ArithFactor ArithmeticFunction

def Harmonic (n : ℕ) : Prop := 0 < n ∧ sigma 1 n ∣ n * n.divisors.card

def Arithmetic (n : ℕ) : Prop := n.divisors.card ∣ sigma 1 n

/-- H(n) = n·d(n)/σ(n). -/
def Hm (n : ℕ) : ℕ := n * n.divisors.card / sigma 1 n

def f1 : PF := [(2, 8), (7, 1), (19, 2), (37, 1), (73, 1), (113, 1), (127, 1)]
def f2 : PF := [(2, 8), (5, 2), (7, 1), (19, 1), (31, 1), (37, 1), (73, 1), (179, 1)]

theorem w_of (f : PF) (n p r : ℕ) (hf : factCheck f = true) (hn : val f = n)
    (hc : (0 < n && n * ndF f % sigF f == 0 && n * ndF f / sigF f == 3 * p &&
      sigF f % ndF f == r && r != 0) = true) :
    Harmonic n ∧ Hm n = 3 * p ∧ sigma 1 n % n.divisors.card = r ∧ ¬ Arithmetic n := by
  have hok := factOK_of_check f hf
  have hs : sigma 1 n = sigF f := by rw [← hn]; exact sigma_val f hok
  have hd : n.divisors.card = ndF f := by rw [← hn]; exact card_divisors_val f hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  refine ⟨⟨h0, ?_⟩, ?_, ?_, ?_⟩
  · rw [hs, hd]; exact Nat.dvd_of_mod_eq_zero h1
  · unfold Hm; rw [hs, hd]; exact h2
  · rw [hs, hd]; exact h3
  · unfold Arithmetic; rw [hs, hd]; intro hdv
    exact h4 (h3 ▸ Nat.mod_eq_zero_of_dvd hdv)

theorem B2_8_main :
    (Harmonic 25075635936512 ∧ Hm 25075635936512 = 3 * 113 ∧ Nat.Prime 113 ∧
      sigma 1 25075635936512 % (Nat.divisors 25075635936512).card = 288 ∧
      ¬ Arithmetic 25075635936512) ∧
    (Harmonic 12757657068800 ∧ Hm 12757657068800 = 3 * 179 ∧ Nat.Prime 179 ∧
      sigma 1 12757657068800 % (Nat.divisors 12757657068800).card = 576 ∧
      ¬ Arithmetic 12757657068800) := by
  obtain ⟨a1, a2, a3, a4⟩ := w_of f1 25075635936512 113 288 (by decide) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨b1, b2, b3, b4⟩ := w_of f2 12757657068800 179 576 (by decide) (by decide +kernel)
    (by decide +kernel)
  exact ⟨⟨a1, a2, by norm_num, a3, a4⟩, ⟨b1, b2, by norm_num, b3, b4⟩⟩

theorem B2_8_false :
    ¬ ∀ n p : ℕ, Harmonic n → p.Prime → Hm n = 3 * p → Arithmetic n := by
  intro h
  obtain ⟨⟨a1, a2, a3, -, a4⟩, -⟩ := B2_8_main
  exact a4 (h _ _ a1 a3 a2)

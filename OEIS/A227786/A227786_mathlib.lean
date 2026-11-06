import Mathlib

/-
OEIS A227786: a(n) = (n+1)^2 - 3 if (n+1)^2 is even, (n+1)^2 - 2 if odd (n >= 1).
Conjecture (entry, Karttunen): from n >= 2 on, a(n) gives the positions of 2's in A227761.

Definitions (as in the entries).
* `topRuns x`: run lengths of the binary expansion of x, most significant run first
  (`Nat.digits 2`, reversed, cut into maximal runs by `rl`).
* `A227183 x`: the runs read from the least significant end, c1, c2, ..., give the parts
  c1, c1 + c2 - 1, c1 + c2 + c3 - 2, ... (`ascParts`); A227183 x is their sum.
* `A227368 N = Nat.find (∃ x, A227183 x = N)` (least such x).
* `A227761 N`: 0 for N < 2, else the maximal difference between successive parts of the
  partition coded by A227368 N (`maxGap`).
* `A227786 n` as in the name.

Main theorem.
* `A227786_conjecture N : A227761 N = 2 ↔ ∃ n, 2 ≤ n ∧ A227786 n = N`.

Route.
* Model: a run list from the top is `R m δ` (top part m, drops δ between consecutive parts);
  its partition is `qs m δ`, with sum m*k - W δ (`qs_sum`), W the weighted drop sum.
* `num_lt`: a shorter run list, or one of equal length that is smaller in the alternating
  lexicographic order `ALT` (odd runs shorter, even runs longer), encodes a smaller integer.
* `model_main`: for the minimal code the length m + k - 1 is minimal over m*k >= N (`LL`),
  the deficiency D = m*k - N is < m and < k (`F4`), the drops are the greedy list `G`
  (`G_opt`), so the largest drop is <= 2 and equals 2 iff D = 2 and k is odd (`G_max`);
  explicit competitor codes (`close_pat`, `dir1`, `dir2`) then leave exactly
  N = k^2 - 2 and N = (k+1)^2 - 3 with k odd.
* Bridge to the integers: `topRuns_spec`, `topRuns_num`, `A227183_num`, `ascParts_R`,
  `maxGap_qs`.
Checked: all of the above, for every N. Not checked: agreement with the OEIS b-files
(certificate/compare.py only). Axioms: propext, Classical.choice, Quot.sound.
-/

namespace OEIS_A227786

/-- `R m δ`: run lengths from the top for top part `m` and drops `δ`. -/
def R : ℕ → List ℕ → List ℕ
  | m, [] => [m]
  | m, d :: ds => (d + 1) :: R (m - d) ds

/-- parts from the top -/
def qs : ℕ → List ℕ → List ℕ
  | m, [] => [m]
  | m, d :: ds => m :: qs (m - d) ds

def W : List ℕ → ℕ
  | [] => 0
  | d :: ds => (ds.length + 1) * d + W ds

def maxE (l : List ℕ) : ℕ := l.foldr max 0

def ALT : Bool → List ℕ → List ℕ → Prop
  | o, a :: l, b :: l' => if a = b then ALT (!o) l l' else (if o then a < b else b < a)
  | _, _, _ => False

def G : Bool → ℕ → ℕ → List ℕ
  | _, 0, _ => []
  | _, 1, D => [D]
  | true, n + 2, D => 0 :: G false (n + 1) D
  | false, n + 2, D => (D / (n + 2)) :: G true (n + 1) (D % (n + 2))

def E : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | n + 1, s, D => (D / (n + 1)) :: E n (s - D / (n + 1)) (D % (n + 1))

def Better (r' r : List ℕ) : Prop :=
  r'.sum < r.sum ∨ (r'.sum = r.sum ∧ ALT true r' r)

theorem ALT_eq (o : Bool) (a : ℕ) (l l' : List ℕ) : ALT o (a :: l) (a :: l') ↔ ALT (!o) l l' := by
  simp [ALT]

theorem ALT_ne (o : Bool) (a b : ℕ) (l l' : List ℕ) (h : a ≠ b) :
    ALT o (a :: l) (b :: l') ↔ (if o then a < b else b < a) := by
  simp [ALT, h]

theorem sum_le_W : ∀ l : List ℕ, l.sum ≤ W l
  | [] => by simp [W]
  | d :: ds => by
    have := sum_le_W ds
    simp only [List.sum_cons, W]
    nlinarith

theorem R_sum : ∀ (δ : List ℕ) (m : ℕ), δ.sum ≤ m → (R m δ).sum = m + δ.length
  | [], m, _ => by simp [R]
  | d :: ds, m, h => by
    simp only [List.sum_cons] at h
    simp only [R, List.sum_cons, List.length_cons]
    rw [R_sum ds (m - d) (by omega)]
    omega

theorem qs_sum : ∀ (δ : List ℕ) (m : ℕ), δ.sum ≤ m →
    (qs m δ).sum + W δ = m * (δ.length + 1)
  | [], m, _ => by simp [qs, W]
  | d :: ds, m, h => by
    simp only [List.sum_cons] at h
    have ih := qs_sum ds (m - d) (by omega)
    simp only [qs, W, List.sum_cons, List.length_cons]
    have hd : d ≤ m := by omega
    obtain ⟨c, rfl⟩ : ∃ c, m = d + c := ⟨m - d, by omega⟩
    rw [show d + c - d = c by omega] at ih ⊢
    nlinarith

theorem qs_ge : ∀ (δ : List ℕ) (m : ℕ), δ.sum < m → m + δ.length ≤ (qs m δ).sum
  | [], m, _ => by simp [qs]
  | d :: ds, m, h => by
    simp only [List.sum_cons] at h
    have ih := qs_ge ds (m - d) (by omega)
    simp only [qs, List.sum_cons, List.length_cons]
    have : 1 ≤ m - d := by omega
    have : 1 ≤ (qs (m - d) ds).sum := by
      cases ds with
      | nil => simp [qs]; omega
      | cons a l => simp [qs]; omega
    omega

theorem R_rep : ∀ (a m : ℕ) (l : List ℕ), R m (List.replicate a 0 ++ l) = List.replicate a 1 ++ R m l
  | 0, m, l => by simp
  | a + 1, m, l => by
    simp [List.replicate_succ, R, R_rep a m l]

theorem ALT_rep2 : ∀ (j : ℕ) (o : Bool) (x : ℕ) (l l' : List ℕ),
    ALT o (List.replicate (2 * j) x ++ l) (List.replicate (2 * j) x ++ l') ↔ ALT o l l'
  | 0, o, x, l, l' => by simp
  | j + 1, o, x, l, l' => by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    simp only [List.replicate_succ, List.cons_append, ALT_eq, Bool.not_not]
    exact ALT_rep2 j o x l l'

theorem ALT_R : ∀ (o : Bool) (δ' δ : List ℕ) (m : ℕ), δ'.length = δ.length →
    ALT o δ' δ → ALT o (R m δ') (R m δ)
  | o, [], [], m, _, h => by simp [ALT] at h
  | o, d' :: ds', d :: ds, m, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [R]
    by_cases hd : d' = d
    · subst hd
      rw [ALT_eq] at h ⊢
      exact ALT_R (!o) ds' ds (m - d') hl h
    · rw [ALT_ne _ _ _ _ _ hd] at h
      rw [ALT_ne _ _ _ _ _ (by omega)]
      cases o <;> simp_all
  | o, [], _ :: _, m, hl, _ => by simp at hl
  | o, _ :: _, [], m, hl, _ => by simp at hl

theorem G_length : ∀ (o : Bool) (n D : ℕ), (G o n D).length = n
  | _, 0, _ => by simp [G]
  | _, 1, D => by simp [G]
  | true, n + 2, D => by simp [G, G_length false (n + 1) D]
  | false, n + 2, D => by simp [G, G_length true (n + 1) (D % (n + 2))]

theorem G_W : ∀ (o : Bool) (n D : ℕ), 1 ≤ n → W (G o n D) = D
  | _, 0, _, h => by omega
  | _, 1, D, _ => by simp [G, W]
  | true, n + 2, D, _ => by simp [G, W, G_W false (n + 1) D (by omega)]
  | false, n + 2, D, _ => by
    simp only [G, W, G_length, G_W true (n + 1) (D % (n + 2)) (by omega)]
    rw [show n + 1 + 1 = n + 2 by ring]
    exact Nat.div_add_mod D (n + 2)

theorem G_le : ∀ (o : Bool) (n D : ℕ), ∀ x ∈ G o n D, x ≤ D
  | _, 0, _ => by simp [G]
  | _, 1, D => by simp [G]
  | true, n + 2, D => by
    intro x hx
    simp only [G, List.mem_cons] at hx
    rcases hx with h | h
    · omega
    · exact G_le false (n + 1) D x h
  | false, n + 2, D => by
    intro x hx
    simp only [G, List.mem_cons] at hx
    rcases hx with h | h
    · subst h; exact Nat.div_le_self _ _
    · exact le_trans (G_le true (n + 1) _ x h) (Nat.mod_le _ _)

theorem G_opt : ∀ (o : Bool) (n D : ℕ) (δ : List ℕ), 1 ≤ n → δ.length = n → W δ = D →
    δ = G o n D ∨ ALT o (G o n D) δ
  | _, 0, _, _, h, _, _ => by omega
  | _, 1, D, δ, _, hl, hW => by
    match δ, hl with
    | [d], _ => simp_all [G, W]
  | true, n + 2, D, δ, _, hl, hW => by
    match δ, hl with
    | d :: ds, hl =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [W, hl] at hW
      by_cases hd : d = 0
      · subst hd
        have := G_opt false (n + 1) D ds (by omega) hl (by simpa using hW)
        rcases this with h | h
        · left; simp [G, h]
        · right; simp only [G]; rw [ALT_eq]; exact h
      · right; simp only [G]; rw [ALT_ne _ _ _ _ _ (by omega)]; simp; omega
  | false, n + 2, D, δ, _, hl, hW => by
    match δ, hl with
    | d :: ds, hl =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [W, hl] at hW
      have hdle : d ≤ D / (n + 2) := by
        rw [Nat.le_div_iff_mul_le (by omega)]; nlinarith
      by_cases hd : d = D / (n + 2)
      · have hr : W ds = D % (n + 2) := by
          have := Nat.div_add_mod D (n + 2)
          rw [← hd] at this
          rw [show n + 1 + 1 = n + 2 by ring] at hW
          nlinarith
        have := G_opt true (n + 1) (D % (n + 2)) ds (by omega) hl hr
        rcases this with h | h
        · left; simp [G, h, hd]
        · right; simp only [G]; rw [← hd, ALT_eq]; simpa using h
      · right; simp only [G]; rw [ALT_ne _ _ _ _ _ (by omega)]; simp; omega

theorem G_skip : ∀ (j n D : ℕ), 1 ≤ n → D < n + 1 →
    G true (n + 2 * j) D = List.replicate (2 * j) 0 ++ G true n D
  | 0, n, D, _, _ => by simp
  | j + 1, n, D, h1, h2 => by
    rw [show n + 2 * (j + 1) = (n + 2 * j + 1) + 1 by ring, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    simp only [G, List.replicate_succ, List.cons_append]
    rw [show n + 2 * j + 1 = (n + 2 * j - 1) + 2 by omega]
    simp only [G]
    rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      show n + 2 * j - 1 + 1 = n + 2 * j by omega, G_skip j n D h1 h2]

theorem maxE_cons (a : ℕ) (l : List ℕ) : maxE (a :: l) = max a (maxE l) := rfl

theorem maxE_le (l : List ℕ) (c : ℕ) (h : ∀ x ∈ l, x ≤ c) : maxE l ≤ c := by
  induction l with
  | nil => simp [maxE]
  | cons a l ih =>
    rw [maxE_cons]
    exact max_le (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem G_max : ∀ n : ℕ, 1 ≤ n →
    (∀ D, D < n + 1 → (maxE (G true n D) = 2 ↔ D = 2 ∧ Even n)) ∧
    (∀ D, D < n + 2 → (maxE (G false n D) = 2 ↔ D = 2 ∧ ¬ Even n))
  | 0, h => by omega
  | 1, _ => by
    refine ⟨fun D hD => ?_, fun D hD => ?_⟩
    · simp [G, maxE]; omega
    · simp [G, maxE]
  | n + 2, _ => by
    refine ⟨fun D hD => ?_, fun D hD => ?_⟩
    · simp only [G]
      rw [maxE_cons]
      have : (maxE (G false (n + 1) D) = 2 ↔ D = 2 ∧ ¬ Even (n + 1)) :=
        (G_max (n + 1) (by omega)).2 D (by omega)
      constructor
      · intro h
        have h' : maxE (G false (n + 1) D) = 2 := by
          rwa [max_eq_right (Nat.zero_le _)] at h
        have := this.1 h'
        refine ⟨this.1, ?_⟩
        rcases Nat.even_or_odd (n + 2) with e | e
        · exact e
        · exfalso; apply this.2; rcases e with ⟨t, ht⟩; exact ⟨t, by omega⟩
      · rintro ⟨h1, h2⟩
        have := this.2 ⟨h1, by rintro ⟨t, ht⟩; rcases h2 with ⟨u, hu⟩; omega⟩
        simp [this]
    · simp only [G]
      rw [maxE_cons]
      by_cases hlt : D < n + 2
      · rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
        have := (G_max (n + 1) (by omega)).1 D (by omega)
        constructor
        · intro h
          have h' : maxE (G true (n + 1) D) = 2 := by
            rwa [max_eq_right (Nat.zero_le _)] at h
          have := this.1 h'
          refine ⟨this.1, ?_⟩
          rintro ⟨t, ht⟩; rcases this.2 with ⟨u, hu⟩; omega
        · rintro ⟨h1, h2⟩
          have hev : Even (n + 1) := by
            rcases Nat.even_or_odd (n + 2) with e | ⟨t, ht⟩
            · exact absurd e h2
            · exact ⟨t, by omega⟩
          simp [this.2 ⟨h1, hev⟩]
      · obtain ⟨e, rfl, he⟩ : ∃ e, D = e + (n + 2) ∧ e < 2 := ⟨D - (n + 2), by omega, by omega⟩
        rw [Nat.add_div_right _ (by omega), Nat.add_mod_right, Nat.div_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
        have hm : maxE (G true (n + 1) e) ≤ 1 := maxE_le _ _ (fun x hx => by
          have := G_le true (n + 1) e x hx; omega)
        constructor
        · intro h; exfalso; simp only [max_def] at h; split_ifs at h <;> omega
        · rintro ⟨h1, h2⟩; exfalso; apply h2; have : n = 0 := by omega
          subst this; decide


theorem E_spec : ∀ (n s D : ℕ), D ≤ s * n →
    (E n s D).length = n ∧ W (E n s D) = D ∧ (E n s D).sum ≤ s
  | 0, s, D, h => by simp [E, W]; omega
  | n + 1, s, D, h => by
    have hq : D / (n + 1) ≤ s := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]; nlinarith
    have hr : D % (n + 1) ≤ (s - D / (n + 1)) * n := by
      by_cases hlt : D / (n + 1) < s
      · have := Nat.mod_lt D (show 0 < n + 1 by omega)
        have : 1 ≤ s - D / (n + 1) := by omega
        nlinarith
      · have he : D / (n + 1) = s := by omega
        have h1 := Nat.div_add_mod D (n + 1)
        rw [he] at h1
        rw [mul_comm] at h
        have : D % (n + 1) = 0 := by omega
        rw [this]; exact Nat.zero_le _
    obtain ⟨h1, h2, h3⟩ := E_spec n (s - D / (n + 1)) (D % (n + 1)) hr
    refine ⟨by simp [E, h1], ?_, ?_⟩
    · simp only [E, W, h1, h2]
      have := Nat.div_add_mod D (n + 1)
      linarith
    · simp only [E, List.sum_cons]; omega

theorem W_rep0 : ∀ a : ℕ, W (List.replicate a 0) = 0
  | 0 => by simp [W]
  | a + 1 => by simp [List.replicate_succ, W, W_rep0 a]

theorem G_pat (j v e : ℕ) (he : e ≤ 1) :
    G true ((v + 3) + 2 * j) (v + 2 + e) = List.replicate (2 * j) 0 ++ 0 :: 1 :: G true (v + 1) e := by
  rw [G_skip j (v + 3) _ (by omega) (by omega)]
  congr 1
  rw [show v + 3 = (v + 1) + 2 by ring]
  simp only [G]
  rw [show v + 1 + 1 = v + 2 by ring, show v + 2 + e = e + (v + 2) by ring,
    Nat.add_div_right _ (by omega), Nat.add_mod_right, Nat.div_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem G22 (i : ℕ) : G true (2 + 2 * i) 2 = List.replicate (2 * i) 0 ++ [0, 2] := by
  rw [G_skip i 2 2 (by omega) (by omega)]; rfl

theorem rep_split (j t : ℕ) (Z : List ℕ) :
    List.replicate (2 * j + 2 + t) 1 ++ Z = List.replicate (2 * j) 1 ++ 1 :: 1 :: (List.replicate t 1 ++ Z) := by
  rw [show 2 * j + 2 + t = 2 * j + (t + 1 + 1) by ring, List.replicate_add, List.append_assoc]
  simp [List.replicate_succ]

theorem ALT_win (j : ℕ) (X Y : List ℕ) :
    ALT true (List.replicate (2 * j) 1 ++ 1 :: 2 :: X) (List.replicate (2 * j) 1 ++ 1 :: 1 :: Y) := by
  rw [ALT_rep2, ALT_eq, ALT_ne _ _ _ _ _ (by omega)]; simp

theorem rep_odd (j x : ℕ) (L : List ℕ) :
    List.replicate (2 * j + 1) x ++ L = List.replicate (2 * j) x ++ x :: L := by
  rw [List.replicate_succ', List.append_assoc]; rfl

theorem close_pat (m' P Dp q j v e t : ℕ) (Z : List ℕ) (he : e ≤ 1) (hP : P = (v + 3) + 2 * j)
    (hD : Dp = v + 2 + e) (hq : q = 2 * j + 2 + t) :
    ALT true (R m' (G true P Dp)) (List.replicate q 1 ++ Z) := by
  subst hP hD hq
  rw [G_pat j v e he, R_rep, rep_split]
  simp only [R, zero_add]
  exact ALT_win j _ _

def Target (N : ℕ) : Prop := ∃ n, 2 ≤ n ∧ N = (n + 1) ^ 2 - 2 - n % 2

theorem pair_sum' (m K J N c : ℕ) (hc : N + c = J * J) (hc3 : c ≤ 3) (hJ : c < J)
    (h1 : m + K ≤ 2 * J) (h2 : N ≤ m * K) : m + K = 2 * J ∧ m + 1 ≥ J ∧ m ≤ J + 1 := by
  have hs : m + K = 2 * J := by
    by_contra hne
    have h1' : m + K + 1 ≤ 2 * J := by omega
    zify at h1' h2 hc hJ
    nlinarith [sq_nonneg ((m : ℤ) - K)]
  refine ⟨hs, ?_, ?_⟩
  · by_contra hne
    have hK : K = 2 * J - m := by omega
    zify at hne h2 hc hc3 hs
    nlinarith
  · by_contra hne
    zify at hne h2 hc hc3 hs
    nlinarith

theorem dir2 (N m k1 D : ℕ) (δ : List ℕ) (_hk1 : δ.length = k1) (hps : N + D = m * (k1 + 1))
    (hG : δ = G true k1 D) (hk1pos : 1 ≤ k1) (hDm : D < m) (_hDk : D < k1 + 1)
    (_LL : ∀ m' k', 1 ≤ m' → 1 ≤ k' → N ≤ m' * k' → m + k1 ≤ m' + k' - 1)
    (F4 : ∀ m' k' D', 2 ≤ m' → 2 ≤ k' → m' + k' = m + k1 + 1 → N + D' = m' * k' →
      D' < m' ∧ D' < k')
    (comp : ∀ m' δ', W δ' + N = m' * (δ'.length + 1) → W δ' < m' →
      m' + δ'.length = m + k1 → ALT true (R m' δ') (R m δ) → False) :
    D = 2 ∧ Even k1 → Target N := by
  rintro ⟨hD2, ⟨i, hi⟩⟩
  have hi1 : 1 ≤ i := by omega
  have hk1i : k1 = 2 + 2 * (i - 1) := by omega
  have hδ : R m δ = List.replicate (2 * i - 1) 1 ++ [3, m - 2] := by
    rw [hG, hk1i, hD2, G22, R_rep, show 2 * i - 1 = 2 * (i - 1) + 1 by omega, rep_odd]; rfl
  rw [hD2] at hps hDm
  have hk2 : k1 = 2 * i := by omega
  rw [hk2] at hps
  rcases (show m ≤ 2 * i ∨ m = 2 * i + 1 ∨ m = 2 * i + 2 ∨ m = 2 * i + 3 ∨ 2 * i + 4 ≤ m by omega)
    with hc | hc | hc | hc | hc
  · -- competitor (m+1, 2i)
    exfalso
    obtain ⟨c, hcm⟩ : ∃ c, 2 * i = m + c := ⟨2 * i - m, by omega⟩
    have hD' : N + (c + 2) = (m + 1) * (2 * i) := by
      rw [hcm] at hps ⊢; nlinarith
    obtain ⟨hA, hB⟩ := F4 (m + 1) (2 * i) _ (by omega) (by omega) (by omega) hD'
    have hc2 : 2 * i - 1 + 1 = 2 * i := by omega
    apply comp (m + 1) (G true (2 * i - 1) (c + 2))
      (by rw [G_W _ _ _ (by omega), G_length, hc2]; omega)
      (by rw [G_W _ _ _ (by omega)]; exact hA) (by rw [G_length]; omega)
    rw [hδ]
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact close_pat _ _ _ _ (t - 2) c 0 (c + 1) _ (by omega) (by omega) (by omega) (by omega)
    · exact close_pat _ _ _ _ (t - 1) (c - 1) 1 c _ (by omega) (by omega) (by omega) (by omega)
  · -- m = k: N = k^2 - 2
    refine ⟨2 * i, by omega, ?_⟩
    rw [hc] at hps
    have : (2 * i + 1) ^ 2 = N + 2 := by nlinarith
    rw [show (2 * i) % 2 = 0 by omega]; omega
  · -- competitor (m+1, 2i-1 drops, all zero)
    exfalso
    have hW := W_rep0 (2 * i - 1)
    apply comp (m + 1) (List.replicate (2 * i - 1) 0)
      (by rw [hW, List.length_replicate, show 2 * i - 1 + 1 = 2 * i by omega, hc]
          rw [hc] at hps; nlinarith)
      (by rw [hW]; omega) (by rw [List.length_replicate]; omega)
    rw [hδ, ← List.append_nil (List.replicate (2 * i - 1) 0), R_rep,
      show 2 * i - 1 = 2 * (i - 1) + 1 by omega, rep_odd, rep_odd]
    simp only [R]
    rw [ALT_rep2, ALT_eq, ALT_ne _ _ _ _ _ (by omega)]
    simp; omega
  · -- m = k + 2: N = (k+1)^2 - 3
    refine ⟨2 * i + 1, by omega, ?_⟩
    rw [hc] at hps
    have : (2 * i + 1 + 1) ^ 2 = N + 3 := by nlinarith
    rw [show (2 * i + 1) % 2 = 1 by omega]; omega
  · -- competitor (m-1, 2i+2)
    exfalso
    obtain ⟨c, hcm⟩ : ∃ c, m = 2 * i + 4 + c := ⟨m - (2 * i + 4), by omega⟩
    have hD' : N + (c + 4) = (m - 1) * (2 * i + 2) := by
      rw [show m - 1 = 2 * i + 3 + c by omega]
      rw [hcm] at hps; nlinarith
    obtain ⟨hA, hB⟩ := F4 (m - 1) (2 * i + 2) _ (by omega) (by omega) (by omega) hD'
    apply comp (m - 1) (G true (2 * i + 1) (c + 4))
      (by rw [G_W _ _ _ (by omega), G_length, show 2 * i + 1 + 1 = 2 * i + 2 by ring]; omega)
      (by rw [G_W _ _ _ (by omega)]; exact hA) (by rw [G_length]; omega)
    rw [hδ]
    rcases Nat.even_or_odd c with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact close_pat _ _ _ _ (i - 2 - t) (c + 2) 0 (c + 1) _ (by omega) (by omega) (by omega) (by omega)
    · exact close_pat _ _ _ _ (i - 2 - t) (c + 1) 1 c _ (by omega) (by omega) (by omega) (by omega)

theorem dir1 (N m k1 D : ℕ) (δ : List ℕ) (_hk1 : δ.length = k1) (hps : N + D = m * (k1 + 1))
    (hG : δ = G true k1 D) (hk1pos : 1 ≤ k1) (_hDm : D < m) (_hDk : D < k1 + 1)
    (LL : ∀ m' k', 1 ≤ m' → 1 ≤ k' → N ≤ m' * k' → m + k1 ≤ m' + k' - 1)
    (_F4 : ∀ m' k' D', 2 ≤ m' → 2 ≤ k' → m' + k' = m + k1 + 1 → N + D' = m' * k' →
      D' < m' ∧ D' < k')
    (comp : ∀ m' δ', W δ' + N = m' * (δ'.length + 1) → W δ' < m' →
      m' + δ'.length = m + k1 → ALT true (R m' δ') (R m δ) → False) :
    Target N → D = 2 ∧ Even k1 := by
  rintro ⟨n, hn2, hN'⟩
  have hK := hps
  rcases Nat.even_or_odd n with ⟨a, ha⟩ | ⟨a, ha⟩
  · -- N = J^2 - 2, J = 2a+1
    have ha1 : 1 ≤ a := by omega
    have hNJ : N + 2 = (2 * a + 1) * (2 * a + 1) := by
      rw [hN', show n % 2 = 0 by omega, ha]
      have : (a + a + 1) ^ 2 = (2 * a + 1) * (2 * a + 1) := by ring
      rw [this]
      have : 4 ≤ (2 * a + 1) * (2 * a + 1) := by nlinarith
      omega
    have hcomp : G true (2 * a) 2 = List.replicate (2 * (a - 1)) 0 ++ [0, 2] := by
      rw [show 2 * a = 2 + 2 * (a - 1) by omega, G22]
    have hL := LL (2 * a + 1) (2 * a + 1) (by omega) (by omega) (by omega)
    obtain ⟨hsum, hmJ1, hmJ2⟩ := pair_sum' m (k1 + 1) (2 * a + 1) N 2 hNJ (by omega) (by omega)
      (by omega) (by omega)
    rcases (show m = 2 * a ∨ m = 2 * a + 1 ∨ m = 2 * a + 2 by omega) with hm | hm | hm
    · -- (J-1, J+1): D = 1, beaten by (J, J)
      exfalso
      have hk : k1 = 2 * a + 1 := by omega
      rw [hm, hk] at hps
      have : (2 * a) * (2 * a + 1 + 1) + 1 = (2 * a + 1) * (2 * a + 1) := by ring
      have hD1 : D = 1 := by omega
      apply comp (2 * a + 1) (G true (2 * a) 2)
        (by rw [G_W _ _ _ (by omega), G_length]; ring_nf; ring_nf at hNJ; omega) (by rw [G_W _ _ _ (by omega)]; omega)
        (by rw [G_length]; omega)
      rw [hcomp, hG, hk, hD1, show 2 * a + 1 = 1 + 2 * a by ring, G_skip a 1 1 (by omega) (by omega),
        R_rep, R_rep, show 2 * a = 2 * (a - 1) + 2 by omega, List.replicate_add, List.append_assoc]
      simp only [R]
      rw [ALT_rep2]
      simp [ALT, G, R]
    · -- (J, J): D = 2, k1 = 2a
      have hk : k1 + 1 = 2 * a + 1 := by omega
      rw [hm, hk] at hps
      refine ⟨by omega, a, by omega⟩
    · -- (J+1, J-1): D = 1, beaten by (J, J)
      exfalso
      have hk : k1 = 2 * a - 1 := by omega
      have hD1 : D = 1 := by
        rw [hm, hk, show 2 * a - 1 + 1 = 2 * a by omega] at hps
        have : (2 * a + 2) * (2 * a) + 1 = (2 * a + 1) * (2 * a + 1) := by ring
        omega
      apply comp (2 * a + 1) (G true (2 * a) 2)
        (by rw [G_W _ _ _ (by omega), G_length]; ring_nf; ring_nf at hNJ; omega) (by rw [G_W _ _ _ (by omega)]; omega)
        (by rw [G_length]; omega)
      rw [hcomp, hG, hk, hD1, show 2 * a - 1 = 1 + 2 * (a - 1) by omega,
        G_skip (a - 1) 1 1 (by omega) (by omega), R_rep, R_rep, hm]
      simp only [R]
      rw [ALT_rep2]
      simp [ALT, G, R]
  · -- N = J^2 - 3, J = 2a+2
    have ha1 : 1 ≤ a := by omega
    have hNJ : N + 3 = (2 * a + 2) * (2 * a + 2) := by
      rw [hN', show n % 2 = 1 by omega, ha]
      have : (2 * a + 1 + 1) ^ 2 = (2 * a + 2) * (2 * a + 2) := by ring
      rw [this]
      have : 4 ≤ (2 * a + 2) * (2 * a + 2) := by nlinarith
      omega
    have hcomp : G true (2 * a) 2 = List.replicate (2 * (a - 1)) 0 ++ [0, 2] := by
      rw [show 2 * a = 2 + 2 * (a - 1) by omega, G22]
    have hJJ : (2 * a + 3) * (2 * a + 1) + 1 = (2 * a + 2) * (2 * a + 2) := by ring
    have hL := LL (2 * a + 3) (2 * a + 1) (by omega) (by omega) (by omega)
    obtain ⟨hsum, hmJ1, hmJ2⟩ := pair_sum' m (k1 + 1) (2 * a + 2) N 3 hNJ (by omega) (by omega)
      (by omega) (by omega)
    rcases (show m = 2 * a + 1 ∨ m = 2 * a + 2 ∨ m = 2 * a + 3 by omega) with hm | hm | hm
    · have hk : k1 = 2 * a + 2 := by omega
      rw [hm, hk] at hps
      have : (2 * a + 1) * (2 * a + 2 + 1) + 1 = (2 * a + 2) * (2 * a + 2) := by ring
      refine ⟨by omega, a + 1, by omega⟩
    · -- (J, J): D = 3, beaten by (J+1, J-1)
      exfalso
      have hk : k1 = 2 * a + 1 := by omega
      rw [hm, hk, show 2 * a + 1 + 1 = 2 * a + 2 by ring] at hps
      have hD3 : D = 3 := by omega
      apply comp (2 * a + 3) (G true (2 * a) 2)
        (by rw [G_W _ _ _ (by omega), G_length]; ring_nf; ring_nf at hNJ; omega) (by rw [G_W _ _ _ (by omega)]; omega)
        (by rw [G_length]; omega)
      rw [hcomp, hG, hk, hD3, show 2 * a + 1 = 3 + 2 * (a - 1) by omega,
        G_skip (a - 1) 3 3 (by omega) (by omega), R_rep, R_rep]
      simp only [R]
      rw [ALT_rep2]
      simp [ALT, G, R]
    · have hk : k1 = 2 * a := by omega
      rw [hm, hk] at hps
      have : (2 * a + 3) * (2 * a + 1) + 1 = (2 * a + 2) * (2 * a + 2) := by ring
      refine ⟨by omega, a, by omega⟩


/-- The combinatorial core: a minimal top-first run list for `N`. -/
theorem model_main (N m : ℕ) (δ : List ℕ) (hV : δ.sum < m) (hN : (qs m δ).sum = N) (h4 : 4 ≤ N)
    (hmin : ∀ m' δ', δ'.sum < m' → (qs m' δ').sum = N → ¬ Better (R m' δ') (R m δ)) :
    (maxE δ = 2 ↔ Target N) := by
  -- competitor principle
  have comp : ∀ m' δ', W δ' + N = m' * (δ'.length + 1) → W δ' < m' →
      m' + δ'.length = m + δ.length → ALT true (R m' δ') (R m δ) → False := by
    intro m' δ' h1 h2 h3 h4
    have hs := sum_le_W δ'
    have hq := qs_sum δ' m' (by omega)
    apply hmin m' δ' (by omega) (by omega)
    right
    rw [R_sum δ' m' (by omega), R_sum δ m (by omega)]
    exact ⟨h3, h4⟩
  set k1 := δ.length with hk1
  set D := W δ with hD
  have hps : N + D = m * (k1 + 1) := by
    have := qs_sum δ m (by omega); rw [← hN]; linarith
  have hge : m + k1 ≤ N := by have := qs_ge δ m hV; omega
  -- length minimality
  have LL : ∀ m' k', 1 ≤ m' → 1 ≤ k' → N ≤ m' * k' → m + k1 ≤ m' + k' - 1 := by
    intro m' k' h1 h2 h3
    by_contra hc
    push Not at hc
    obtain ⟨a, rfl⟩ : ∃ a, m' = a + 1 := ⟨m' - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, k' = b + 1 := ⟨k' - 1, by omega⟩
    have hD' : (a + 1) * (b + 1) - N ≤ a * b := by
      have : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
      omega
    obtain ⟨e1, e2, e3⟩ := E_spec b a ((a + 1) * (b + 1) - N) hD'
    have hq := qs_sum (E b a ((a + 1) * (b + 1) - N)) (a + 1) (by omega)
    rw [e1, e2] at hq
    apply hmin (a + 1) (E b a ((a + 1) * (b + 1) - N)) (by omega) (by omega)
    left
    rw [R_sum _ _ (by omega), R_sum δ m (by omega), e1]
    omega
  -- m, k1 large
  have hk1pos : 1 ≤ k1 := by
    by_contra hc
    have hk0 : k1 = 0 := by omega
    have := LL 2 ((N + 1) / 2) (by omega) (by omega) (by omega)
    rw [hk0] at hps
    omega
  have hm2 : 2 ≤ m := by
    by_contra hc
    have hm1 : m = 1 := by omega
    have := LL 2 ((N + 1) / 2) (by omega) (by omega) (by omega)
    rw [hm1] at hps
    omega
  have F4 : ∀ m' k' D', 2 ≤ m' → 2 ≤ k' → m' + k' = m + k1 + 1 → N + D' = m' * k' →
      D' < m' ∧ D' < k' := by
    intro m' k' D' h1 h2 h3 h5
    constructor
    · by_contra hc
      have := LL m' (k' - 1) (by omega) (by omega) (by
        have : m' * (k' - 1) + m' = m' * k' := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega)
      omega
    · by_contra hc
      have := LL (m' - 1) k' (by omega) (by omega) (by
        have : (m' - 1) * k' + k' = m' * k' := by
          rw [← Nat.succ_mul]; congr 1; omega
        omega)
      omega
  obtain ⟨hDm, hDk⟩ := F4 m (k1 + 1) D hm2 (by omega) (by omega) hps
  -- the minimal list is greedy
  have hG : δ = G true k1 D := by
    rcases G_opt true k1 D δ hk1pos rfl rfl with h | h
    · exact h
    · exfalso
      apply comp m (G true k1 D) (by rw [G_W _ _ _ hk1pos, G_length]; omega)
        (by rw [G_W _ _ _ hk1pos]; exact hDm) (by rw [G_length])
      exact ALT_R true _ _ m (by rw [G_length]) h
  have hmax : maxE δ = 2 ↔ D = 2 ∧ Even k1 := by
    rw [hG]; exact (G_max k1 hk1pos).1 D hDk
  rw [hmax]
  exact ⟨dir2 N m k1 D δ rfl hps hG hk1pos hDm hDk LL F4 comp, dir1 N m k1 D δ rfl hps hG hk1pos hDm hDk LL F4 comp⟩


/-! ## Binary run lengths and the OEIS definitions -/

/-- `rlAux d c l`: run lengths of `d^c ++ l` (digits left to right). -/
def rlAux : ℕ → ℕ → List ℕ → List ℕ
  | _, c, [] => [c]
  | d, c, e :: l => if e = d then rlAux d (c + 1) l else c :: rlAux e 1 l

/-- run lengths of a digit list, left to right -/
def rl : List ℕ → List ℕ
  | [] => []
  | d :: l => rlAux d 1 l

/-- run lengths of the binary expansion of `x`, from the most significant end -/
def topRuns (x : ℕ) : List ℕ := rl (Nat.digits 2 x).reverse

def ascGo : ℕ → List ℕ → List ℕ
  | p, [] => [p]
  | p, c :: cs => p :: ascGo (p + c - 1) cs

/-- A129594 / A227183 encoding: runs `c₁, c₂, …` read from the least significant end give the
parts `c₁, c₁ + c₂ - 1, c₁ + c₂ + c₃ - 2, …` (partial sums of `c₁, c₂ - 1, c₃ - 1, …`). -/
def ascParts : List ℕ → List ℕ
  | [] => []
  | c :: cs => ascGo c cs

/-- A227183(x): sum of the parts of the partition encoded by the runs of `x`. -/
def A227183 (x : ℕ) : ℕ := (ascParts (topRuns x).reverse).sum

/-- maximal difference between successive parts -/
def maxGap : List ℕ → ℕ
  | a :: b :: l => max (b - a) (maxGap (b :: l))
  | _ => 0

/-- binary digits (most significant first) for runs `r`, starting with digit `d` -/
def enc : ℕ → List ℕ → List ℕ
  | _, [] => []
  | d, a :: l => List.replicate a d ++ enc (1 - d) l

def num (r : List ℕ) : ℕ := Nat.ofDigits 2 (enc 1 r).reverse

def Pos (r : List ℕ) : Prop := r ≠ [] ∧ ∀ x ∈ r, 1 ≤ x

theorem rlAux_rep (d c a : ℕ) (l : List ℕ) :
    rlAux d c (List.replicate a d ++ l) = rlAux d (c + a) l := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [rlAux, ↓reduceIte]
    rw [ih]; congr 1; omega

theorem rlAux_enc : ∀ (r : List ℕ) (d c : ℕ), d ≤ 1 → (∀ x ∈ r, 1 ≤ x) →
    rlAux d c (enc (1 - d) r) = c :: r
  | [], d, c, _, _ => by simp [enc, rlAux]
  | a :: l, d, c, hd, hp => by
    have ha : 1 ≤ a := hp a (by simp)
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [enc, List.replicate_succ, List.cons_append, rlAux]
    have hne : ¬ (1 - d = d) := by omega
    simp only [hne, ↓reduceIte]
    rw [rlAux_rep]
    have := rlAux_enc l (1 - d) (1 + b) (by omega) (fun x hx => hp x (by simp [hx]))
    rw [this]; congr 2; ring

theorem rl_enc (r : List ℕ) (hr : Pos r) : rl (enc 1 r) = r := by
  obtain ⟨hne, hp⟩ := hr
  match r, hne with
  | a :: l, _ =>
    have ha : 1 ≤ a := hp a (by simp)
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [enc, List.replicate_succ, List.cons_append, rl]
    rw [rlAux_rep]
    have := rlAux_enc l 1 (1 + b) (by omega) (fun x hx => hp x (by simp [hx]))
    simp only [Nat.sub_self] at this
    rw [show (1 : ℕ) - 1 = 0 from rfl, this]; congr 1; ring

theorem enc_mem : ∀ (r : List ℕ) (d : ℕ), d ≤ 1 → ∀ x ∈ enc d r, x ≤ 1
  | [], d, _ => by simp [enc]
  | a :: l, d, hd => by
    intro x hx
    simp only [enc, List.mem_append, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | hx
    · exact hd
    · exact enc_mem l (1 - d) (by omega) x hx

theorem enc_length : ∀ (r : List ℕ) (d : ℕ), (enc d r).length = r.sum
  | [], d => by simp [enc]
  | a :: l, d => by simp [enc, enc_length l]

theorem enc_head (d b : ℕ) (l : List ℕ) (hb : 1 ≤ b) :
    enc d (b :: l) = d :: (List.replicate (b - 1) d ++ enc (1 - d) l) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  simp [enc, List.replicate_succ]

theorem digits_num (r : List ℕ) (hr : Pos r) : Nat.digits 2 (num r) = (enc 1 r).reverse := by
  apply Nat.digits_ofDigits 2 (by norm_num)
  · intro x hx
    rw [List.mem_reverse] at hx
    have := enc_mem r 1 le_rfl x hx; omega
  · intro h
    obtain ⟨hne, hp⟩ := hr
    match r, hne with
    | a :: l, _ =>
      rw [List.getLast_reverse]
      simp [enc_head 1 a l (hp a (by simp))]

theorem topRuns_num (r : List ℕ) (hr : Pos r) : topRuns (num r) = r := by
  rw [topRuns, digits_num r hr, List.reverse_reverse, rl_enc r hr]

theorem enc_rlAux : ∀ (l : List ℕ) (d c : ℕ), d ≤ 1 → (∀ x ∈ l, x ≤ 1) →
    enc d (rlAux d c l) = List.replicate c d ++ l
  | [], d, c, _, _ => by simp [rlAux, enc]
  | e :: l, d, c, hd, hl => by
    simp only [rlAux]
    by_cases he : e = d
    · simp only [he, ↓reduceIte]
      rw [enc_rlAux l d (c + 1) hd (fun x hx => hl x (by simp [hx])),
        List.replicate_succ', List.append_assoc]; rfl
    · simp only [he, ↓reduceIte]
      have he' : e = 1 - d := by have := hl e (by simp); omega
      simp only [enc]
      rw [← he', enc_rlAux l e 1 (by omega) (fun x hx => hl x (by simp [hx]))]
      simp

theorem rlAux_pos : ∀ (l : List ℕ) (d c : ℕ), 1 ≤ c → ∀ x ∈ rlAux d c l, 1 ≤ x
  | [], d, c, hc => by simp [rlAux]; omega
  | e :: l, d, c, hc => by
    simp only [rlAux]
    split_ifs
    · exact rlAux_pos l d (c + 1) (by omega)
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hc
      · exact rlAux_pos l e 1 le_rfl x hx

theorem rlAux_ne (l : List ℕ) (d c : ℕ) : rlAux d c l ≠ [] := by
  cases l with
  | nil => simp [rlAux]
  | cons e l => simp only [rlAux]; split_ifs <;> simp [rlAux_ne]

theorem topRuns_spec (x : ℕ) (hx : x ≠ 0) : Pos (topRuns x) ∧ num (topRuns x) = x := by
  have hlast := Nat.getLast_digit_ne_zero 2 hx
  have hlt : ∀ y ∈ Nat.digits 2 x, y ≤ 1 := fun y hy => by
    have := Nat.digits_lt_base (by norm_num) hy; omega
  have hne : Nat.digits 2 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hx
  obtain ⟨M, hM⟩ : ∃ M, (Nat.digits 2 x).reverse = 1 :: M := by
    match h : (Nat.digits 2 x).reverse with
    | [] => simp at h; exact absurd h hne
    | a :: M =>
      refine ⟨M, ?_⟩
      have h1 : (Nat.digits 2 x).getLast hne = a := by
        rw [← List.head_reverse (by simpa using hne)]; simp [h]
      have h2 := hlt a (by rw [← List.mem_reverse, h]; simp)
      have : a ≠ 0 := h1 ▸ hlast
      congr 1; omega
  have hMl : ∀ y ∈ M, y ≤ 1 := fun y hy => hlt y (by rw [← List.mem_reverse, hM]; simp [hy])
  have ht : topRuns x = rlAux 1 1 M := by rw [topRuns, hM]; rfl
  refine ⟨⟨by rw [ht]; exact rlAux_ne _ _ _, by rw [ht]; exact rlAux_pos M 1 1 le_rfl⟩, ?_⟩
  rw [num, ht, enc_rlAux M 1 1 le_rfl hMl]
  have : List.replicate 1 1 ++ M = (Nat.digits 2 x).reverse := by rw [hM]; rfl
  rw [this, List.reverse_reverse, Nat.ofDigits_digits]

theorem R_pos : ∀ (δ : List ℕ) (m : ℕ), δ.sum < m → Pos (R m δ)
  | [], m, h => ⟨by simp [R], by simp [R]; omega⟩
  | d :: ds, m, h => by
    simp only [List.sum_cons] at h
    obtain ⟨_, h2⟩ := R_pos ds (m - d) (by omega)
    refine ⟨by simp [R], ?_⟩
    intro x hx
    simp only [R, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact h2 x hx

theorem R_decomp : ∀ (r : List ℕ), Pos r → ∃ m δ, r = R m δ ∧ δ.sum < m
  | [], h => absurd rfl h.1
  | [a], h => ⟨a, [], by simp [R], by have := h.2 a (by simp); simp; omega⟩
  | a :: b :: l, h => by
    obtain ⟨m', δ', h1, h2⟩ := R_decomp (b :: l) ⟨by simp, fun x hx => h.2 x (by simp_all)⟩
    have ha := h.2 a (by simp)
    refine ⟨m' + (a - 1), (a - 1) :: δ', ?_, by simp; omega⟩
    simp only [R]
    rw [show m' + (a - 1) - (a - 1) = m' by omega, ← h1, show a - 1 + 1 = a by omega]

theorem ascGo_snoc : ∀ (cs : List ℕ) (p y : ℕ),
    ascGo p (cs ++ [y]) = ascGo p cs ++ [(ascGo p cs).getLastD 0 + y - 1]
  | [], p, y => by simp [ascGo]
  | c :: cs, p, y => by
    simp only [List.cons_append, ascGo]
    rw [ascGo_snoc cs]
    cases cs <;> simp [ascGo]

theorem qs_ne (m : ℕ) (δ : List ℕ) : ∃ t, qs m δ = m :: t := by
  cases δ with
  | nil => exact ⟨[], rfl⟩
  | cons d ds => exact ⟨qs (m - d) ds, rfl⟩

theorem qs_rev_last (m : ℕ) (δ : List ℕ) : (qs m δ).reverse.getLastD 0 = m := by
  obtain ⟨t, ht⟩ := qs_ne m δ
  rw [ht, List.reverse_cons, List.getLastD_concat]

theorem ascParts_R : ∀ (δ : List ℕ) (m : ℕ), δ.sum < m →
    ascParts (R m δ).reverse = (qs m δ).reverse
  | [], m, _ => by simp [R, qs, ascParts, ascGo]
  | d :: ds, m, h => by
    simp only [List.sum_cons] at h
    have ih := ascParts_R ds (m - d) (by omega)
    have hrev : (R (m - d) ds).reverse ≠ [] := by
      simpa using (R_pos ds (m - d) (by omega)).1
    obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hrev
    have hA : ascGo c cs = ascParts (R (m - d) ds).reverse := by rw [hc]; rfl
    simp only [R, qs, List.reverse_cons]
    rw [hc, List.cons_append]
    show ascGo c (cs ++ [d + 1]) = _
    rw [ascGo_snoc, hA, ih, qs_rev_last]
    congr 2; omega

theorem maxGap_snoc : ∀ (X : List ℕ) (y : ℕ), X ≠ [] →
    maxGap (X ++ [y]) = max (maxGap X) (y - X.getLastD 0)
  | [], _, h => absurd rfl h
  | [a], y, _ => by simp [maxGap]
  | a :: b :: l, y, _ => by
    simp only [List.cons_append, maxGap]
    rw [← List.cons_append, maxGap_snoc (b :: l) y (by simp), max_assoc]
    simp

theorem maxGap_qs : ∀ (δ : List ℕ) (m : ℕ), δ.sum ≤ m → maxGap (qs m δ).reverse = maxE δ
  | [], m, _ => by simp [qs, maxGap, maxE]
  | d :: ds, m, h => by
    simp only [List.sum_cons] at h
    simp only [qs, List.reverse_cons]
    obtain ⟨t, ht⟩ := qs_ne (m - d) ds
    rw [maxGap_snoc _ _ (by simp [ht]), maxGap_qs ds (m - d) (by omega), qs_rev_last, maxE_cons,
      show m - (m - d) = d by omega, max_comm]

theorem maxE_le_sum (l : List ℕ) : maxE l ≤ l.sum :=
  maxE_le l _ (fun _ hx => List.le_sum_of_mem hx)

/-! value comparison -/

def V (L : List ℕ) : ℕ := Nat.ofDigits 2 L.reverse

def lexLT : List ℕ → List ℕ → Prop
  | a :: L, b :: L' => a < b ∨ (a = b ∧ lexLT L L')
  | _, _ => False

theorem V_cons (a : ℕ) (L : List ℕ) : V (a :: L) = V L + 2 ^ L.length * a := by
  simp [V, Nat.ofDigits_append, Nat.ofDigits_singleton]

theorem V_lt (L : List ℕ) (h : ∀ x ∈ L, x ≤ 1) : V L < 2 ^ L.length := by
  have := Nat.ofDigits_lt_base_pow_length (b := 2) (l := L.reverse) (by norm_num)
    (fun x hx => by have := h x (List.mem_reverse.mp hx); omega)
  simpa [V] using this

theorem V_lex : ∀ (L L' : List ℕ), L.length = L'.length → (∀ x ∈ L, x ≤ 1) → (∀ x ∈ L', x ≤ 1) →
    lexLT L L' → V L < V L'
  | [], [], _, _, _, h => by simp [lexLT] at h
  | a :: L, b :: L', hl, h1, h2, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [V_cons, V_cons, hl]
    rcases h with h | ⟨rfl, h⟩
    · have := V_lt L (fun x hx => h1 x (by simp [hx]))
      rw [hl] at this
      have : 2 ^ L'.length * a + 2 ^ L'.length ≤ 2 ^ L'.length * b := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
      omega
    · have := V_lex L L' (by omega) (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx])) h
      omega
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

theorem lex_rep (a d : ℕ) (X Y : List ℕ) :
    lexLT (List.replicate a d ++ X) (List.replicate a d ++ Y) ↔ lexLT X Y := by
  induction a with
  | zero => simp
  | succ a ih => simp [List.replicate_succ, lexLT, ih]

theorem enc_lex : ∀ (o : Bool) (r' r : List ℕ), (∀ x ∈ r', 1 ≤ x) → (∀ x ∈ r, 1 ≤ x) →
    r'.sum = r.sum → ALT o r' r → lexLT (enc (if o then 1 else 0) r') (enc (if o then 1 else 0) r)
  | o, [], [], _, _, _, h => by simp [ALT] at h
  | o, a' :: l', a :: l, h1, h2, hs, h => by
    simp only [List.sum_cons] at hs
    by_cases he : a' = a
    · subst he
      rw [ALT_eq] at h
      simp only [enc]
      rw [lex_rep]
      have := enc_lex (!o) l' l (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx]))
        (by omega) h
      cases o <;> simpa using this
    · rw [ALT_ne _ _ _ _ _ he] at h
      cases o
      · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨b, l2, hl⟩ := List.exists_cons_of_ne_nil (show l ≠ [] by
          rintro rfl; simp at hs; omega)
        subst hl
        have hb := h2 b (by simp)
        obtain ⟨c, rfl⟩ : ∃ c, a' = a + (c + 1) := ⟨a' - a - 1, by omega⟩
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        simp only [enc]
        rw [show List.replicate (a + (c + 1)) 0 = List.replicate a 0 ++ List.replicate (c + 1) 0 by
          rw [List.replicate_add], List.append_assoc, lex_rep]
        simp [List.replicate_succ, lexLT]
      · simp only [↓reduceIte] at h ⊢
        obtain ⟨b, l2, hl⟩ := List.exists_cons_of_ne_nil (show l' ≠ [] by
          rintro rfl; simp at hs; omega)
        subst hl
        have hb := h1 b (by simp)
        obtain ⟨c, rfl⟩ : ∃ c, a = a' + (c + 1) := ⟨a - a' - 1, by omega⟩
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        simp only [enc]
        rw [show List.replicate (a' + (c + 1)) 1 = List.replicate a' 1 ++ List.replicate (c + 1) 1 by
          rw [List.replicate_add], List.append_assoc, lex_rep]
        simp [List.replicate_succ, lexLT]
  | o, [], _ :: _, _, _, _, h => by simp [ALT] at h
  | o, _ :: _, [], _, _, _, h => by simp [ALT] at h

theorem num_lt (r' r : List ℕ) (h' : Pos r') (h : Pos r) (hb : Better r' r) : num r' < num r := by
  have hm' := enc_mem r' 1 le_rfl
  have hm := enc_mem r 1 le_rfl
  rcases hb with hlt | ⟨heq, halt⟩
  · have h1 := V_lt (enc 1 r') hm'
    rw [enc_length] at h1
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil h.1
    have ha := h.2 a (by simp)
    have h2 : 2 ^ (enc 1 (a :: l)).length ≤ 2 * V (enc 1 (a :: l)) := by
      rw [enc_head 1 a l ha, V_cons, List.length_cons, pow_succ]
      simp only [mul_one]
      omega
    rw [enc_length] at h2
    have h3 : 2 ^ r'.sum * 2 ≤ 2 ^ (a :: l).sum := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) hlt
    show V (enc 1 r') < V (enc 1 (a :: l))
    omega
  · show V (enc 1 r') < V (enc 1 r)
    apply V_lex _ _ (by rw [enc_length, enc_length, heq]) hm' hm
    simpa using enc_lex true r' r h'.2 h.2 heq halt

theorem A227183_num (m : ℕ) (δ : List ℕ) (h : δ.sum < m) :
    A227183 (num (R m δ)) = (qs m δ).sum := by
  rw [A227183, topRuns_num _ (R_pos δ m h), ascParts_R δ m h, List.sum_reverse]

theorem A227183_exists (N : ℕ) : ∃ x, A227183 x = N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, by simp [A227183, topRuns, rl, ascParts]⟩
  · exact ⟨num (R N []), by rw [A227183_num N [] (by simpa using hN)]; simp [qs]⟩

/-- A227368(n): least `x` with A227183(x) = n. -/
noncomputable def A227368 (N : ℕ) : ℕ := Nat.find (A227183_exists N)

/-- A227761(n): maximal difference between successive parts of the partition coded by A227368(n)
(0 for n < 2, as in the entry). -/
noncomputable def A227761 (N : ℕ) : ℕ :=
  if N < 2 then 0 else maxGap (ascParts (topRuns (A227368 N)).reverse)

/-- A227786: squares larger than 1, minus 3 if even and minus 2 if odd. -/
def A227786 (n : ℕ) : ℕ := if Even ((n + 1) ^ 2) then (n + 1) ^ 2 - 3 else (n + 1) ^ 2 - 2

theorem A227786_eq (n : ℕ) : A227786 n = (n + 1) ^ 2 - 2 - n % 2 := by
  unfold A227786
  rcases Nat.even_or_odd n with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have : ¬ Even ((a + a + 1) ^ 2) := by
      rw [Nat.even_pow]; rintro ⟨⟨t, ht⟩, _⟩; omega
    simp only [this, ↓reduceIte]; rw [show (a + a) % 2 = 0 by omega]; omega
  · have : Even ((2 * a + 1 + 1) ^ 2) := by
      rw [Nat.even_pow]; exact ⟨⟨a + 1, by ring⟩, by norm_num⟩
    simp only [this, ↓reduceIte]; rw [show (2 * a + 1) % 2 = 1 by omega]; omega

/-- Conjecture of A227786 (Karttunen): from n = 2 on, A227786 lists exactly the positions of 2 in
A227761. -/
theorem A227786_conjecture (N : ℕ) : A227761 N = 2 ↔ ∃ n, 2 ≤ n ∧ A227786 n = N := by
  have hT : (∃ n, 2 ≤ n ∧ A227786 n = N) ↔ Target N := by
    simp only [Target, A227786_eq]
    exact ⟨fun ⟨n, h1, h2⟩ => ⟨n, h1, h2.symm⟩, fun ⟨n, h1, h2⟩ => ⟨n, h1, h2.symm⟩⟩
  rw [hT]
  by_cases hN2 : N < 2
  · simp only [A227761, hN2, ↓reduceIte]
    constructor
    · intro h; omega
    · rintro ⟨n, hn, rfl⟩
      exfalso
      have : 9 ≤ (n + 1) ^ 2 := by nlinarith
      omega
  simp only [A227761, hN2, ↓reduceIte]
  set x := A227368 N with hxdef
  have hx : A227183 x = N := Nat.find_spec (A227183_exists N)
  have hxmin : ∀ y, A227183 y = N → x ≤ y := fun y hy => Nat.find_min' _ hy
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0] at hx; simp [A227183, topRuns, rl, ascParts] at hx; omega
  obtain ⟨hpos, hnum⟩ := topRuns_spec x hx0
  obtain ⟨m, δ, hr, hV⟩ := R_decomp _ hpos
  have hN : (qs m δ).sum = N := by
    rw [← hx, ← hnum, hr, A227183_num m δ hV]
  rw [hr, ascParts_R δ m hV, maxGap_qs δ m (by omega)]
  by_cases h4 : 4 ≤ N
  · apply model_main N m δ hV hN h4
    intro m' δ' hV' hN' hb
    have hlt := num_lt _ _ (R_pos δ' m' hV') (R_pos δ m hV) hb
    rw [← hr, hnum] at hlt
    have := hxmin _ (by rw [A227183_num m' δ' hV', hN'])
    omega
  · constructor
    · intro h
      exfalso
      have h1 := maxE_le_sum δ
      have h2 := qs_ge δ m hV
      have h3 : δ ≠ [] := by rintro rfl; simp [maxE] at h
      have h4' : 1 ≤ δ.length := by cases δ <;> simp_all
      omega
    · rintro ⟨n, hn, rfl⟩
      exfalso
      have : 9 ≤ (n + 1) ^ 2 := by nlinarith
      omega

end OEIS_A227786

open OEIS_A227786

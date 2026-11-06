/-
OEIS A192023 (Wiener index of the comb graph |_|_|...|_| with 2n nodes).
Kimberling's comment (determinant 2n) is false; see A192023.lean. This file proves the
corrected form, from Kimberling's own table in A211795 (relation w = -x + y + z + 2):

  `A192023_main`: for n >= 2,
    #{(w, x, y, z) in {1..n}^4 : w + x = y + z + 2} = Wiener index of the comb with 2(n-1) nodes.

Pieces:
  * `A192023_linear`: the count equals a(n-1), a(m) = m (2 m^2 + 6 m - 5) / 3 (n >= 1);
  * `A192023_dist`: graph distance in the comb (`A192023_comb`, Mathlib `SimpleGraph.dist`)
    equals the explicit formula `A192023_D`;
  * `A192023_wiener_eq`: the Wiener index (half the sum of `dist` over ordered pairs)
    equals a(n) for n >= 1 (the entry's formula).
Everything is proved in Lean; the modelling choice is the vertex set Fin n x Fin 2 with
(i, 0) on the spine and (i, 1) the tooth on (i, 0).
-/
import Mathlib

open Finset

/-- The OEIS closed form a(m) = m (2 m^2 + 6 m - 5) / 3. -/
def A192023_a (m : ℕ) : ℕ := m * (2 * m ^ 2 + 6 * m - 5) / 3

/-- Pairs (w, x) in {1..n}^2. -/
def A192023_P (n : ℕ) : Finset (ℕ × ℕ) := Icc 1 n ×ˢ Icc 1 n

/-- Number of (w, x) in {1..n}^2 with w + x = t. -/
def A192023_r (n t : ℕ) : ℕ := #{p ∈ A192023_P n | p.1 + p.2 = t}

/-- The count in the conjecture. -/
def A192023_C (n : ℕ) : ℕ := #{q ∈ A192023_P n ×ˢ A192023_P n | q.1.1 + q.1.2 = q.2.1 + q.2.2 + 2}

lemma A192023_r_eq (n t : ℕ) : A192023_r n t = min n (t - 1) + 1 - max 1 (t - n) := by
  have h : A192023_r n t = #{w ∈ Icc 1 n | w < t ∧ t ≤ w + n} := by
    unfold A192023_r
    apply Finset.card_bij (fun p _ => p.1)
    · intro p hp
      simp only [A192023_P, mem_filter, mem_product, mem_Icc] at hp ⊢
      omega
    · intro p hp q hq hpq
      simp only [A192023_P, mem_filter, mem_product, mem_Icc] at hp hq
      ext <;> omega
    · intro w hw
      simp only [mem_filter, mem_Icc] at hw
      refine ⟨(w, t - w), ?_, rfl⟩
      simp only [A192023_P, mem_filter, mem_product, mem_Icc]
      omega
  rw [h]
  have h2 : ({w ∈ Icc 1 n | w < t ∧ t ≤ w + n} : Finset ℕ) =
      Icc (max 1 (t - n)) (min n (t - 1)) := by
    ext w
    simp only [mem_filter, mem_Icc]
    omega
  rw [h2, Nat.card_Icc]

lemma A192023_C_eq_sum (n : ℕ) : A192023_C n = ∑ t ∈ Icc 2 (2 * n), A192023_r n t * A192023_r n (t + 2) := by
  have h1 : A192023_C n = ∑ q ∈ A192023_P n, A192023_r n (q.1 + q.2 + 2) := by
    unfold A192023_C A192023_r
    rw [card_filter, sum_product_right]
    refine sum_congr rfl (fun q _ => ?_)
    rw [card_filter]
  rw [h1, ← sum_fiberwise_of_maps_to (g := fun q : ℕ × ℕ => q.1 + q.2) (t := Icc 2 (2 * n))]
  · refine sum_congr rfl (fun t _ => ?_)
    rw [sum_congr rfl (g := fun _ => A192023_r n (t + 2))]
    · rw [sum_const, smul_eq_mul]
      rfl
    · intro q hq
      simp only [mem_filter] at hq
      rw [hq.2]
  · intro q hq
    simp only [A192023_P, mem_product, mem_Icc] at hq ⊢
    omega

lemma A192023_sumA (k : ℕ) : 6 * ∑ s ∈ range k, (s + 1) * (s + 3) = k * (k + 1) * (2 * k + 7) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

lemma A192023_C_formula (k : ℕ) :
    A192023_C (k + 2) = 2 * ∑ s ∈ range k, (s + 1) * (s + 3) + (k + 1) ^ 2 := by
  rw [A192023_C_eq_sum, show Icc 2 (2 * (k + 2)) = Ico 2 (2 * k + 5) by
    ext x; simp only [mem_Icc, mem_Ico]; omega, sum_Ico_eq_sum_range,
    show 2 * k + 5 - 2 = k + (k + 3) by omega, sum_range_add]
  have hA : ∑ s ∈ range k, A192023_r (k + 2) (2 + s) * A192023_r (k + 2) (2 + s + 2) =
      ∑ s ∈ range k, (s + 1) * (s + 3) := by
    refine sum_congr rfl (fun s hs => ?_)
    simp only [mem_range] at hs
    rw [A192023_r_eq, A192023_r_eq]
    congr 1 <;> omega
  have hB : ∑ x ∈ range (k + 3), A192023_r (k + 2) (2 + (k + x)) * A192023_r (k + 2) (2 + (k + x) + 2) =
      (k + 1) ^ 2 + ∑ s ∈ range k, (s + 1) * (s + 3) := by
    rw [sum_range_succ', sum_range_succ, sum_range_succ]
    have e0 : A192023_r (k + 2) (2 + (k + 0)) * A192023_r (k + 2) (2 + (k + 0) + 2) = (k + 1) ^ 2 := by
      rw [A192023_r_eq, A192023_r_eq, sq]
      congr 1 <;> omega
    have e1 : A192023_r (k + 2) (2 + (k + (k + 1))) * A192023_r (k + 2) (2 + (k + (k + 1)) + 2) = 0 := by
      rw [A192023_r_eq (k + 2) (2 + (k + (k + 1)) + 2)]
      rw [show min (k + 2) (2 + (k + (k + 1)) + 2 - 1) + 1 - max 1 (2 + (k + (k + 1)) + 2 - (k + 2))
        = 0 by omega, mul_zero]
    have e2 : A192023_r (k + 2) (2 + (k + (k + 1 + 1))) * A192023_r (k + 2) (2 + (k + (k + 1 + 1)) + 2) = 0 := by
      rw [A192023_r_eq (k + 2) (2 + (k + (k + 1 + 1)) + 2)]
      rw [show min (k + 2) (2 + (k + (k + 1 + 1)) + 2 - 1) + 1 - max 1 (2 + (k + (k + 1 + 1)) + 2 - (k + 2))
        = 0 by omega, mul_zero]
    rw [e0, e1, e2]
    have e3 : ∑ x ∈ range k, A192023_r (k + 2) (2 + (k + (x + 1))) * A192023_r (k + 2) (2 + (k + (x + 1)) + 2) =
        ∑ x ∈ range k, (k + 2 - x) * (k - x) := by
      refine sum_congr rfl (fun x hx => ?_)
      simp only [mem_range] at hx
      rw [A192023_r_eq, A192023_r_eq]
      congr 1 <;> omega
    rw [e3, ← sum_range_reflect]
    have e4 : ∑ j ∈ range k, (k + 2 - (k - 1 - j)) * (k - (k - 1 - j)) =
        ∑ s ∈ range k, (s + 1) * (s + 3) := by
      refine sum_congr rfl (fun j hj => ?_)
      simp only [mem_range] at hj
      rw [mul_comm]
      congr 1 <;> omega
    rw [e4]
    ring
  rw [hA, hB]
  ring

theorem A192023_linear (n : ℕ) (hn : 1 ≤ n) :
    #{q ∈ (Icc 1 n ×ˢ Icc 1 n) ×ˢ (Icc 1 n ×ˢ Icc 1 n) |
        q.1.1 + q.1.2 = q.2.1 + q.2.2 + 2} = A192023_a (n - 1) := by
  change A192023_C n = A192023_a (n - 1)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rcases k with _ | k
  · decide
  · rw [show k + 1 + 1 = k + 2 by ring, A192023_C_formula, show k + 2 - 1 = k + 1 by omega]
    unfold A192023_a
    have hs := A192023_sumA k
    have hsub : 2 * (k + 1) ^ 2 + 6 * (k + 1) - 5 = 2 * k ^ 2 + 10 * k + 3 := by
      have : 2 * (k + 1) ^ 2 + 6 * (k + 1) = 2 * k ^ 2 + 10 * k + 3 + 5 := by ring
      omega
    rw [hsub]
    symm
    apply Nat.div_eq_of_eq_mul_left (by norm_num)
    nlinarith [hs]


/-! ## The comb graph and its Wiener index

Vertices (i, t) with i < n, t < 2: (i, 0) on the spine path, (i, 1) the tooth on (i, 0). -/

/-- The comb graph |_|_|...|_| with 2n vertices. -/
def A192023_comb (n : ℕ) : SimpleGraph (Fin n × Fin 2) where
  Adj u v := (u.2.val = 0 ∧ v.2.val = 0 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val)) ∨
    (u.1.val = v.1.val ∧ u.2.val ≠ v.2.val)
  symm := ⟨by
    intro u v h
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr ⟨h1.symm, Ne.symm h2⟩⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨_, _, h⟩ | ⟨_, h⟩
    · omega
    · exact h rfl⟩

/-- Explicit distance in the comb. -/
def A192023_D {n : ℕ} (u v : Fin n × Fin 2) : ℕ :=
  if u.1.val = v.1.val then (if u.2.val = v.2.val then 0 else 1)
  else (u.1.val - v.1.val) + (v.1.val - u.1.val) + u.2.val + v.2.val

lemma A192023_D_lip {n : ℕ} {u w : Fin n × Fin 2} (v : Fin n × Fin 2)
    (h : (A192023_comb n).Adj u w) : A192023_D u v ≤ A192023_D w v + 1 := by
  have hu := u.2.isLt
  have hw := w.2.isLt
  have hv := v.2.isLt
  simp only [A192023_comb] at h
  unfold A192023_D
  split_ifs <;> omega

lemma A192023_D_lower {n : ℕ} {u v : Fin n × Fin 2} (p : (A192023_comb n).Walk u v) :
    A192023_D u v ≤ p.length := by
  induction p with
  | nil => simp [A192023_D]
  | @cons x y z h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    have := A192023_D_lip z h
    omega

lemma A192023_D_step {n : ℕ} (m : ℕ) (u v : Fin n × Fin 2) (hd : A192023_D u v = m + 1) :
    ∃ w, (A192023_comb n).Adj u w ∧ A192023_D w v = m := by
  obtain ⟨⟨i, hi⟩, ⟨a, ha⟩⟩ := u
  obtain ⟨⟨j, hj⟩, ⟨b, hb⟩⟩ := v
  unfold A192023_D at hd
  simp only at hd
  by_cases ha1 : a = 1
  · refine ⟨((⟨i, hi⟩ : Fin n), (0 : Fin 2)), ?_, ?_⟩
    · exact Or.inr ⟨rfl, show a ≠ 0 by omega⟩
    · simp only [A192023_D, Fin.val_zero]; split_ifs at hd ⊢ <;> omega
  · by_cases hij : i = j
    · refine ⟨((⟨i, hi⟩ : Fin n), (1 : Fin 2)), ?_, ?_⟩
      · exact Or.inr ⟨rfl, show a ≠ 1 by omega⟩
      · simp only [A192023_D, Fin.val_one]; split_ifs at hd ⊢ <;> omega
    · by_cases hlt : i < j
      · refine ⟨((⟨i + 1, by omega⟩ : Fin n), (0 : Fin 2)), ?_, ?_⟩
        · exact Or.inl ⟨show a = 0 by omega, rfl, Or.inl rfl⟩
        · simp only [A192023_D, Fin.val_zero]; split_ifs at hd ⊢ <;> omega
      · refine ⟨((⟨i - 1, by omega⟩ : Fin n), (0 : Fin 2)), ?_, ?_⟩
        · exact Or.inl ⟨show a = 0 by omega, rfl, Or.inr (show i - 1 + 1 = i by omega)⟩
        · simp only [A192023_D, Fin.val_zero]; split_ifs at hd ⊢ <;> omega

lemma A192023_D_upper {n : ℕ} (m : ℕ) : ∀ u v : Fin n × Fin 2, A192023_D u v = m →
    ∃ p : (A192023_comb n).Walk u v, p.length = m := by
  induction m with
  | zero =>
    intro u v hd
    have huv : u = v := by
      obtain ⟨⟨i, hi⟩, ⟨a, ha⟩⟩ := u
      obtain ⟨⟨j, hj⟩, ⟨b, hb⟩⟩ := v
      unfold A192023_D at hd
      simp only at hd
      split_ifs at hd with h1 h2
      · simp [h1, h2]
      · omega
    subst huv
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ m ih =>
    intro u v hd
    obtain ⟨w, hw, hwd⟩ := A192023_D_step m u v hd
    obtain ⟨p, hp⟩ := ih w v hwd
    exact ⟨SimpleGraph.Walk.cons hw p, by rw [SimpleGraph.Walk.length_cons, hp]⟩

theorem A192023_dist {n : ℕ} (u v : Fin n × Fin 2) :
    (A192023_comb n).dist u v = A192023_D u v := by
  obtain ⟨p, hp⟩ := A192023_D_upper (A192023_D u v) u v rfl
  apply le_antisymm
  · rw [← hp]; exact SimpleGraph.dist_le p
  · obtain ⟨q, hq⟩ := (SimpleGraph.Walk.reachable p).exists_walk_length_eq_dist
    rw [← hq]; exact A192023_D_lower q

/-- Wiener index: sum of distances over unordered pairs, i.e. half the ordered sum. -/
noncomputable def A192023_wiener (n : ℕ) : ℕ :=
  (∑ u : Fin n × Fin 2, ∑ v : Fin n × Fin 2, (A192023_comb n).dist u v) / 2

/-- Sum of distances between the four vertex pairs over columns i and j. -/
def A192023_g (i j : ℕ) : ℕ := 4 * ((i - j) + (j - i)) + 2 + 2 * (if i = j then 0 else 1)

lemma A192023_inner (i j : ℕ) :
    (∑ a : Fin 2, ∑ b : Fin 2,
      (if i = j then (if a.val = b.val then 0 else 1)
       else (i - j) + (j - i) + a.val + b.val)) = A192023_g i j := by
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, A192023_g]
  split_ifs <;> omega

lemma A192023_rowsum (n : ℕ) : 2 * ∑ j ∈ range n, ((n - j) + (j - n)) = n * (n + 1) := by
  have e : ∑ j ∈ range n, ((n - j) + (j - n)) = ∑ j ∈ range n, (j + 1) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl (fun j hj => ?_)
    simp only [mem_range] at hj
    omega
  rw [e]
  clear e
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, mul_add, ih]; ring

lemma A192023_total (n : ℕ) :
    3 * (∑ i ∈ range n, ∑ j ∈ range n, A192023_g i j) + 10 * n = 4 * n ^ 3 + 12 * n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have split : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), A192023_g i j =
        ∑ i ∈ range n, ∑ j ∈ range n, A192023_g i j + ∑ i ∈ range n, A192023_g i n +
          ∑ j ∈ range n, A192023_g n j + A192023_g n n := by
      simp only [sum_range_succ, sum_add_distrib]
      ring
    have c4 : 4 * n = ∑ i ∈ range n, 4 := by rw [sum_const, card_range, smul_eq_mul, mul_comm]
    have r1 : ∑ i ∈ range n, A192023_g i n = 4 * ∑ j ∈ range n, ((n - j) + (j - n)) + 4 * n := by
      rw [mul_sum, c4, ← sum_add_distrib]
      refine sum_congr rfl (fun i hi => ?_)
      simp only [mem_range] at hi
      simp only [A192023_g]
      split_ifs <;> omega
    have r2 : ∑ j ∈ range n, A192023_g n j = 4 * ∑ j ∈ range n, ((n - j) + (j - n)) + 4 * n := by
      rw [mul_sum, c4, ← sum_add_distrib]
      refine sum_congr rfl (fun j hj => ?_)
      simp only [mem_range] at hj
      simp only [A192023_g]
      split_ifs <;> omega
    have r3 : A192023_g n n = 2 := by simp [A192023_g]
    have hR := A192023_rowsum n
    rw [split, r1, r2, r3]
    nlinarith [ih, hR]

theorem A192023_wiener_eq (n : ℕ) (hn : 1 ≤ n) : A192023_wiener n = A192023_a n := by
  unfold A192023_wiener A192023_a
  simp only [A192023_dist]
  have h1 : ∀ i j : Fin n, ∑ a : Fin 2, ∑ b : Fin 2, A192023_D (i, a) (j, b) =
      A192023_g i.val j.val := by
    intro i j
    unfold A192023_D
    exact A192023_inner i.val j.val
  have hsum : (∑ u : Fin n × Fin 2, ∑ v : Fin n × Fin 2, A192023_D u v) =
      ∑ i ∈ range n, ∑ j ∈ range n, A192023_g i j := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    calc (∑ i : Fin n, ∑ a : Fin 2, ∑ j : Fin n, ∑ b : Fin 2, A192023_D (i, a) (j, b))
        = ∑ i : Fin n, ∑ j : Fin n, A192023_g i.val j.val := by
          refine sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
          exact sum_congr rfl (fun j _ => h1 i j)
      _ = ∑ i : Fin n, ∑ j ∈ range n, A192023_g i.val j := by
          refine sum_congr rfl (fun i _ => ?_)
          exact Fin.sum_univ_eq_sum_range (fun j => A192023_g i.val j) n
      _ = ∑ i ∈ range n, ∑ j ∈ range n, A192023_g i j :=
          Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, A192023_g i j) n
  rw [hsum]
  have ht := A192023_total n
  have h5 : 5 ≤ 2 * n ^ 2 + 6 * n := by nlinarith
  have hA : n * (2 * n ^ 2 + 6 * n - 5) + 5 * n = 2 * n ^ 3 + 6 * n ^ 2 := by
    have e5 : 2 * n ^ 2 + 6 * n - 5 + 5 = 2 * n ^ 2 + 6 * n := Nat.sub_add_cancel h5
    calc n * (2 * n ^ 2 + 6 * n - 5) + 5 * n = n * (2 * n ^ 2 + 6 * n - 5 + 5) := by ring
      _ = 2 * n ^ 3 + 6 * n ^ 2 := by rw [e5]; ring
  generalize n * (2 * n ^ 2 + 6 * n - 5) = A at hA ⊢
  generalize ∑ i ∈ range n, ∑ j ∈ range n, A192023_g i j = T at ht ⊢
  generalize n ^ 3 = X at hA ht
  generalize n ^ 2 = Y at hA ht
  omega

theorem A192023_main (n : ℕ) (hn : 2 ≤ n) :
    #{q ∈ (Icc 1 n ×ˢ Icc 1 n) ×ˢ (Icc 1 n ×ˢ Icc 1 n) |
        q.1.1 + q.1.2 = q.2.1 + q.2.2 + 2} = A192023_wiener (n - 1) := by
  rw [A192023_linear n (by omega), A192023_wiener_eq (n - 1) (by omega)]

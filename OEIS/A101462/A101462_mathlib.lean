import OpenProblemsLib

/-
OEIS A101462 (Mathlib). a(n) = smallest k with 2^k - prime(n) prime. Conjecture: a(n) exists
for every n. README result: false, prime(42228) = 509203 and 2^k - 509203 is never prime.

Main theorem `A101462_main`: `Nat.nth Nat.Prime 42227 = 509203` (Mathlib's `Nat.nth` is
0-indexed, so this is prime(42228) = 509203 in the OEIS 1-indexed convention), and for every k,
`2 ^ k - Nat.nth Nat.Prime 42227` is not prime. Subtraction is in ℕ, so for k ≤ 18 the value is
0 (the integer 2^k - 509203 is negative, hence also not a prime). `A101462_conjecture_false`
is the negation of "for every n some 2^k - prime(n) is prime".

Proof.
* Covering congruence (restated from the core file lean): for k ≥ 19 one of
  3, 5, 7, 13, 17, 241 divides 2^k - 509203 and is smaller than it.
* The index: `Nat.count Nat.Prime 509203 = 42227` by a kernel computation. With L the 127
  primes below 714 (each prime by trial division, `primeTD`; and every prime below 714 is
  in L) and Q their product, a k with 710 ≤ k < 714^2 is prime iff gcd(k, Q) = 1
  (`prime_iff_gcd`). The count of such k in [712, 509203) is evaluated by `decide +kernel`
  in 509 blocks of 999, and the 127 primes below 712 are counted from L.

Outside Lean: nothing.
-/

open OpenProblemsLib.ArithFactor


/-! ### The covering congruence (from lean) -/

def P : Nat := 509203

/-- (q, o, a): o = ord_q(2), and q ∣ 2^k - P whenever k ≡ a (mod o). -/
def cover : List (Nat × Nat × Nat) :=
  [(3, 2, 0), (5, 4, 3), (7, 3, 1), (13, 12, 5), (17, 8, 1), (241, 24, 21)]

theorem cover_orders : cover.all (fun t => 2 ^ t.2.1 % t.1 == 1) = true := by decide
theorem cover_classes : cover.all (fun t => 2 ^ t.2.2 % t.1 == P % t.1) = true := by decide
theorem cover_periods : cover.all (fun t => 24 % t.2.1 == 0) = true := by decide
theorem cover_small : cover.all (fun t => decide (2 ≤ t.1 ∧ t.1 ≤ 241 ∧ t.2.2 < t.2.1)) = true := by
  decide
theorem cover_all : (List.range 24).all (fun r => cover.any (fun t => r % t.2.1 == t.2.2)) = true := by
  decide

theorem pow_period (q o n : Nat) (ho : 2 ^ o % q = 1) : 2 ^ n % q = 2 ^ (n % o) % q := by
  have h := Nat.div_add_mod n o
  conv => lhs; rw [← h, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, ho, Nat.one_pow]
  have hq : q ≠ 1 := by
    intro h1; rw [h1, Nat.mod_one] at ho; exact absurd ho (by decide)
  cases q with
  | zero => simp
  | succ q' =>
    have : 1 % (q' + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.one_mul, Nat.mod_mod]

theorem cover_divides (k : Nat) (hk : 19 ≤ k) :
    ∃ t ∈ cover, t.1 ∣ 2 ^ k - P ∧ 1 < t.1 ∧ t.1 < 2 ^ k - P := by
  have hr : k % 24 ∈ List.range 24 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have h1 := List.all_eq_true.mp cover_all _ hr
  obtain ⟨t, ht, hcls⟩ := List.any_eq_true.mp h1
  have hs := List.all_eq_true.mp cover_small t ht
  simp only [decide_eq_true_eq] at hs
  have hbig : 2 ^ 19 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have h19 : 2 ^ 19 = 524288 := by decide
  have hP : P = 509203 := rfl
  refine ⟨t, ht, ?_, by omega, by omega⟩
  have ho : 2 ^ t.2.1 % t.1 = 1 := by simpa using List.all_eq_true.mp cover_orders t ht
  have hc : 2 ^ t.2.2 % t.1 = P % t.1 := by simpa using List.all_eq_true.mp cover_classes t ht
  have hd : t.2.1 ∣ 24 :=
    Nat.dvd_of_mod_eq_zero (by simpa using List.all_eq_true.mp cover_periods t ht)
  have hcl : k % 24 % t.2.1 = t.2.2 := by simpa using hcls
  have hn : k % t.2.1 = t.2.2 := by rw [← Nat.mod_mod_of_dvd k hd]; exact hcl
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [pow_period t.1 t.2.1 k ho, hn, hc]

theorem never_prime (k : ℕ) : ¬ (2 ^ k - 509203).Prime := by
  by_cases hk : 19 ≤ k
  · obtain ⟨t, _, hd, h1, h2⟩ := cover_divides k hk
    intro hp
    rcases hp.eq_one_or_self_of_dvd _ hd with h | h
    · omega
    · exact absurd h (by simp only [P] at h2; omega)
  · have h1 : 2 ^ k ≤ 2 ^ 18 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ k - 509203 = 0 := by
      have : (2 : ℕ) ^ 18 = 262144 := by decide
      omega
    rw [h2]; exact Nat.not_prime_zero

/-! ### The index: π(509203) = 42228 -/

/-- The primes below 714. -/
def L : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709]

/-- The product of L. -/
def Q : ℕ := 13802651106711802536344050306133362992649963656229914863058580142142610482430817949922104531639351381921564573865712490763569228376295661814770390189505137031692781919527713285374540164408571278055683171593020170233128086464775974520546386806644011091046992108509661969860784773011026549129761870

theorem Q_eq : Q = L.prod := by decide +kernel

theorem L_prime : ∀ p ∈ L, p.Prime := by
  have h : L.all primeTD = true := by decide +kernel
  intro p hp
  exact prime_of_primeTD p (List.all_eq_true.mp h p hp)

theorem L_lt : ∀ p ∈ L, p < 710 := by
  have h : L.all (fun p => decide (p < 710)) = true := by decide +kernel
  intro p hp
  simpa using List.all_eq_true.mp h p hp

/-- Every q < 714 is in L, or is < 2, or has a divisor d ∈ L with d < q. -/
theorem L_check : (List.range 714).all (fun q => decide (q < 2) || L.contains q ||
    L.any (fun d => decide (d < q) && q % d == 0)) = true := by decide +kernel

theorem L_complete (q : ℕ) (hq : q < 714) (hp : q.Prime) : q ∈ L := by
  have h := List.all_eq_true.mp L_check q (List.mem_range.mpr hq)
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | ⟨d, hd, hdq, hm⟩
  · exact absurd hp.two_le (by omega)
  · exact h
  · exfalso
    have h2 := (L_prime d hd).two_le
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hm) with h | h <;> omega

theorem small_prime_iff (k : ℕ) (hk : k < 714) : k.Prime ↔ L.contains k = true := by
  rw [List.contains_iff_mem]
  exact ⟨L_complete k hk, fun h => L_prime k h⟩

theorem prime_iff_gcd (k : ℕ) (h1 : 710 ≤ k) (h2 : k < 714 * 714) :
    k.Prime ↔ (Nat.gcd k Q == 1) = true := by
  rw [beq_iff_eq, Q_eq]
  constructor
  · intro hk
    apply Nat.coprime_list_prod_right_iff.mpr
    intro n hn
    have := L_lt n hn
    exact (Nat.coprime_primes hk (L_prime n hn)).mpr (by omega)
  · intro hg
    by_contra hk
    have hk1 : k ≠ 1 := by omega
    have hr := Nat.minFac_prime hk1
    by_cases hr7 : k.minFac < 714
    · have hmem := L_complete _ hr7 hr
      have hd : k.minFac ∣ Nat.gcd k L.prod :=
        Nat.dvd_gcd (Nat.minFac_dvd k) (List.dvd_prod hmem)
      rw [hg] at hd
      exact hr.one_lt.ne' (Nat.dvd_one.mp hd)
    · have hsq := Nat.minFac_sq_le_self (by omega) hk
      have : 714 * 714 ≤ k.minFac ^ 2 := by
        rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
      omega

/-! ### Counting by kernel evaluation -/

def cnt (f : ℕ → Bool) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => cnt f a i + (if f (a + i) then 1 else 0)

def blk (f : ℕ → Bool) (a B : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => blk f a B j + cnt f (a + B * j) B

theorem count_cnt (f : ℕ → Bool) (a : ℕ) :
    ∀ n, Nat.count (fun i => f (a + i) = true) n = cnt f a n
  | 0 => by simp [cnt]
  | n + 1 => by rw [Nat.count_succ, count_cnt f a n, cnt]

theorem count_blk (f : ℕ → Bool) (a B : ℕ) :
    ∀ m, Nat.count (fun i => f (a + i) = true) (B * m) = blk f a B m
  | 0 => by simp [blk]
  | m + 1 => by
    rw [Nat.mul_succ, Nat.count_add, count_blk f a B m, blk]
    congr 1
    rw [← count_cnt]
    simp only [Nat.add_assoc]

theorem count_congr' {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] :
    ∀ n, (∀ i < n, (p i ↔ q i)) → Nat.count p n = Nat.count q n
  | 0, _ => by simp
  | n + 1, h => by
    rw [Nat.count_succ, Nat.count_succ, count_congr' n (fun i hi => h i (by omega))]
    by_cases hp : p n
    · simp [hp, (h n (by omega)).mp hp]
    · have : ¬ q n := fun hq => hp ((h n (by omega)).mpr hq)
      simp [hp, this]

theorem count_712 : Nat.count Nat.Prime 712 = 127 := by
  rw [count_congr' (q := fun i => L.contains (0 + i) = true) 712
    (fun i hi => by rw [Nat.zero_add]; exact small_prime_iff i (by omega))]
  rw [count_cnt (fun k => L.contains k) 0 712]
  decide +kernel

/-- `blk` splits at m₁ blocks. -/
theorem blk_split (f : ℕ → Bool) (a B m₁ : ℕ) :
    ∀ m₂, blk f a B (m₁ + m₂) = blk f a B m₁ + blk f (a + B * m₁) B m₂
  | 0 => by simp [blk]
  | m₂ + 1 => by
    rw [← Nat.add_assoc, blk, blk_split f a B m₁ m₂, blk, Nat.add_assoc, Nat.mul_add,
      Nat.add_assoc]

def gq (k : ℕ) : Bool := Nat.gcd k Q == 1

theorem chunk_0 : blk gq 712 999 20 = 2202 := by decide +kernel
theorem chunk_1 : blk gq 20692 999 20 = 1931 := by decide +kernel
theorem chunk_2 : blk gq 40672 999 20 = 1854 := by decide +kernel
theorem chunk_3 : blk gq 60652 999 20 = 1776 := by decide +kernel
theorem chunk_4 : blk gq 80632 999 20 = 1753 := by decide +kernel
theorem chunk_5 : blk gq 100612 999 20 = 1705 := by decide +kernel
theorem chunk_6 : blk gq 120592 999 20 = 1709 := by decide +kernel
theorem chunk_7 : blk gq 140572 999 20 = 1669 := by decide +kernel
theorem chunk_8 : blk gq 160552 999 20 = 1659 := by decide +kernel
theorem chunk_9 : blk gq 180532 999 20 = 1640 := by decide +kernel
theorem chunk_10 : blk gq 200512 999 20 = 1628 := by decide +kernel
theorem chunk_11 : blk gq 220492 999 20 = 1605 := by decide +kernel
theorem chunk_12 : blk gq 240472 999 20 = 1611 := by decide +kernel
theorem chunk_13 : blk gq 260452 999 20 = 1597 := by decide +kernel
theorem chunk_14 : blk gq 280432 999 20 = 1562 := by decide +kernel
theorem chunk_15 : blk gq 300412 999 20 = 1616 := by decide +kernel
theorem chunk_16 : blk gq 320392 999 20 = 1567 := by decide +kernel
theorem chunk_17 : blk gq 340372 999 20 = 1574 := by decide +kernel
theorem chunk_18 : blk gq 360352 999 20 = 1541 := by decide +kernel
theorem chunk_19 : blk gq 380332 999 20 = 1559 := by decide +kernel
theorem chunk_20 : blk gq 400312 999 20 = 1523 := by decide +kernel
theorem chunk_21 : blk gq 420292 999 20 = 1553 := by decide +kernel
theorem chunk_22 : blk gq 440272 999 20 = 1518 := by decide +kernel
theorem chunk_23 : blk gq 460252 999 20 = 1547 := by decide +kernel
theorem chunk_24 : blk gq 480232 999 20 = 1529 := by decide +kernel
theorem chunk_25 : blk gq 500212 999 9 = 672 := by decide +kernel

theorem blk_total : blk gq 712 999 509 = 42100 := by
  have s0 := blk_split gq 712 999 20 489
  norm_num only at s0
  have s1 := blk_split gq 20692 999 20 469
  norm_num only at s1
  have s2 := blk_split gq 40672 999 20 449
  norm_num only at s2
  have s3 := blk_split gq 60652 999 20 429
  norm_num only at s3
  have s4 := blk_split gq 80632 999 20 409
  norm_num only at s4
  have s5 := blk_split gq 100612 999 20 389
  norm_num only at s5
  have s6 := blk_split gq 120592 999 20 369
  norm_num only at s6
  have s7 := blk_split gq 140572 999 20 349
  norm_num only at s7
  have s8 := blk_split gq 160552 999 20 329
  norm_num only at s8
  have s9 := blk_split gq 180532 999 20 309
  norm_num only at s9
  have s10 := blk_split gq 200512 999 20 289
  norm_num only at s10
  have s11 := blk_split gq 220492 999 20 269
  norm_num only at s11
  have s12 := blk_split gq 240472 999 20 249
  norm_num only at s12
  have s13 := blk_split gq 260452 999 20 229
  norm_num only at s13
  have s14 := blk_split gq 280432 999 20 209
  norm_num only at s14
  have s15 := blk_split gq 300412 999 20 189
  norm_num only at s15
  have s16 := blk_split gq 320392 999 20 169
  norm_num only at s16
  have s17 := blk_split gq 340372 999 20 149
  norm_num only at s17
  have s18 := blk_split gq 360352 999 20 129
  norm_num only at s18
  have s19 := blk_split gq 380332 999 20 109
  norm_num only at s19
  have s20 := blk_split gq 400312 999 20 89
  norm_num only at s20
  have s21 := blk_split gq 420292 999 20 69
  norm_num only at s21
  have s22 := blk_split gq 440272 999 20 49
  norm_num only at s22
  have s23 := blk_split gq 460252 999 20 29
  norm_num only at s23
  have s24 := blk_split gq 480232 999 20 9
  norm_num only at s24
  rw [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  rw [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25]

theorem count_rest : Nat.count (fun k => Nat.Prime (712 + k)) (999 * 509) = 42100 := by
  rw [count_congr' (q := fun i => gq (712 + i) = true) (999 * 509)
    (fun i hi => prime_iff_gcd (712 + i) (by omega) (by omega))]
  rw [← blk_total]
  exact count_blk gq 712 999 509

theorem count_P : Nat.count Nat.Prime 509203 = 42227 := by
  have e : (509203 : ℕ) = 712 + 999 * 509 := by norm_num
  rw [e, Nat.count_add, count_712, count_rest]

theorem P_prime : Nat.Prime 509203 := prime_of_primeTD 509203 (by decide +kernel)

theorem nth_P : Nat.nth Nat.Prime 42227 = 509203 := by
  rw [← count_P]; exact Nat.nth_count P_prime


theorem A101462_main : Nat.nth Nat.Prime 42227 = 509203 ∧
    ∀ k : ℕ, ¬ (2 ^ k - Nat.nth Nat.Prime 42227).Prime := by
  refine ⟨nth_P, fun k => ?_⟩
  rw [nth_P]; exact never_prime k

theorem A101462_conjecture_false : ¬ ∀ n : ℕ, ∃ k : ℕ, (2 ^ k - Nat.nth Nat.Prime n).Prime := by
  intro h
  obtain ⟨k, hk⟩ := h 42227
  exact A101462_main.2 k hk

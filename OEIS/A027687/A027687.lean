/-
OEIS A027687 (4-perfect numbers, sigma(N) = 4N). Conjecture (Ianakiev, 2013):
A010888(a(n)) divides a(n), where A010888 is the digital root.

Checked here:
* `dr` is the digital root as defined in A010888 (repeated decimal digit sum until
  one digit remains), and `dr_eq`: dr N = 0 for N = 0, else 1 + (N - 1) % 9.
* `dr_dvd_of_six_dvd`: dr N ∣ N for every N with 6 ∣ N. So the conjecture holds
  for every 4-perfect number divisible by 6.
* `known_six_dvd`: the 36 known 4-perfect numbers (b-file b027687.txt) are all
  divisible by 6, hence `known_conjecture`: dr N ∣ N for each of them.
Not checked here: that these 36 numbers are 4-perfect and that no others exist
(the list's completeness is open); 4-perfect numbers not divisible by 6 (none known,
odd ones not excluded) are not covered.
-/

def ds (n : Nat) : Nat :=
  if n < 10 then n else n % 10 + ds (n / 10)
termination_by n
decreasing_by omega

theorem ds_mod (n : Nat) : ds n % 9 = n % 9 := by
  unfold ds
  split
  · rfl
  · have ih := ds_mod (n / 10)
    omega
termination_by n
decreasing_by omega

theorem ds_lt (n : Nat) (h : 10 ≤ n) : ds n < n := by
  unfold ds
  split
  · omega
  have hle : ∀ m, ds m ≤ m := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      unfold ds
      split
      · omega
      · have := ih (m / 10) (by omega)
        omega
  have := hle (n / 10)
  omega

theorem ds_pos (n : Nat) (h : 0 < n) : 0 < ds n := by
  unfold ds
  split
  · omega
  · have ih := ds_pos (n / 10)
    by_cases h10 : n % 10 = 0
    · have : 0 < n / 10 := by omega
      have := ih this
      omega
    · omega
termination_by n
decreasing_by omega

/-- Digital root (A010888): repeated digit sum until one digit remains. -/
def dr (n : Nat) : Nat :=
  if _h : n < 10 then n else dr (ds n)
termination_by n
decreasing_by exact ds_lt n (by omega)

theorem dr_eq (n : Nat) : dr n = if n = 0 then 0 else 1 + (n - 1) % 9 := by
  unfold dr
  split
  · split <;> omega
  · have ih := dr_eq (ds n)
    rw [ih]
    have hm := ds_mod n
    have hp := ds_pos n (by omega)
    split <;> split <;> omega
termination_by n
decreasing_by exact ds_lt n (by omega)

theorem dr_dvd_of_six_dvd (N : Nat) (h : 6 ∣ N) : dr N ∣ N := by
  rw [dr_eq]
  obtain ⟨k, rfl⟩ := h
  by_cases hk : k = 0
  · subst hk; simp
  · split
    · omega
    have : (6 * k - 1) % 9 = 8 ∨ (6 * k - 1) % 9 = 5 ∨ (6 * k - 1) % 9 = 2 := by omega
    rcases this with h | h | h <;> rw [h] <;> exact Nat.dvd_of_mod_eq_zero (by omega)

/-- The 36 known 4-perfect numbers (OEIS b-file b027687.txt). -/
def known : List Nat :=
  [30240,
   32760,
   2178540,
   23569920,
   45532800,
   142990848,
   1379454720,
   43861478400,
   66433720320,
   153003540480,
   403031236608,
   704575228896,
   181742883469056,
   6088728021160320,
   14942123276641920,
   20158185857531904,
   275502900594021408,
   622286506811515392,
   71065075104190073088,
   203820700083634254643200,
   63583020166602943198789632,
   156036748944739017459105792,
   1612532860097932682386735104,
   3638193973609385308194865152,
   24862223033124742964111030747136,
   27255271098894367673389500334080,
   61013466228291299819132525346816,
   66886157385030640039109307924480,
   630532357710420079508428362350592,
   1422606063264005633932239197700096,
   1928622300236318049928258133164032,
   58234847911585743639191150258791907328,
   142911996309794733796329290979468115968,
   21571439852601139426707905057216142508032,
   651350717502447739281012140234441171379683328,
   1598455815964665104598224777343146075218771968]

theorem known_six_dvd : known.all (fun N => N % 6 == 0) = true := by decide

theorem known_conjecture : ∀ N ∈ known, dr N ∣ N := by
  intro N hN
  apply dr_dvd_of_six_dvd
  have h := List.all_eq_true.mp known_six_dvd N hN
  exact Nat.dvd_of_mod_eq_zero (by simpa using h)

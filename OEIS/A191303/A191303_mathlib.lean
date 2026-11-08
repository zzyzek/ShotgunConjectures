import Mathlib

/-
OEIS A191303 (Vladimir Shevelev): "Conjecture. For every k>=2, there exists a polynomial of
degree k taking only k-digit half-palindrome values."  Definition (A191279): m is a k-digit
half-palindrome if there are bases 1 < b < c with m = [m_1 m_2 ... m_k]_b = [m_k ... m_1]_c,
the m_i digits in both bases, m_1 > 0 and m_k > 0.  The entry says the question is open for
every k >= 5 (polynomials known for k <= 4).

Checked here: `A191303_k5` ... `A191303_k11`, `A191303_k13`: for k = 5, ..., 11 and 13 an explicit polynomial P_k of
degree k in s (positive leading coefficient) such that P_k(s) is a k-digit half-palindrome for
every s : ℕ, with c = b + 1 (k >= 6) or c = b + 2 (k = 5) and b and all digits linear in s.
Not checked here: k = 12 and k >= 14 (open; see README for the searched ranges); k <= 4 (in the entry).
`valB b ds` is the value of the digit list ds (most significant first) in base b.
-/

def valB (b : ℕ) (ds : List ℕ) : ℕ := ds.foldl (fun acc x => acc * b + x) 0

def HalfPal (k m : ℕ) : Prop :=
  ∃ b c : ℕ, ∃ ds : List ℕ, ds.length = k ∧ 1 < b ∧ b < c ∧ (∀ x ∈ ds, x < b) ∧
    0 < ds.headD 0 ∧ 0 < ds.getLastD 0 ∧ m = valB b ds ∧ m = valB c ds.reverse

def P5 (s : ℕ) : ℕ := 4096*s^5 + 36864*s^4 + 132224*s^3 + 236288*s^2 + 210409*s + 74705

theorem A191303_k5 (s : ℕ) : HalfPal 5 (P5 s) := by
  refine ⟨8*s + 14, 8*s + 16, [s + 1, 8*s + 13, 2*s + 3, 2, s + 1], rfl, by omega, by omega, ?_,
    by simp, by simp, ?_, ?_⟩
  · intro x hx; simp at hx; omega
  · simp [valB, P5]; ring
  · simp [valB, P5]; ring

def P6 (s : ℕ) : ℕ := 32*s^6 + 512*s^5 + 3376*s^4 + 11744*s^3 + 22742*s^2 + 23263*s + 9831

theorem A191303_k6 (s : ℕ) : HalfPal 6 (P6 s) := by
  refine ⟨2*s + 5, 2*s + 6, [s + 3, s, 2*s + 3, 3, 1, s + 1], rfl, by omega, by omega, ?_,
    by simp, by simp, ?_, ?_⟩
  · intro x hx; simp at hx; omega
  · simp [valB, P6]; ring
  · simp [valB, P6]; ring

def P7 (s : ℕ) : ℕ := 64*s^7 + 1696*s^6 + 19168*s^5 + 119768*s^4 + 446848*s^3 + 995562*s^2 + 1226575*s + 644765

theorem A191303_k7 (s : ℕ) : HalfPal 7 (P7 s) := by
  refine ⟨2*s + 7, 2*s + 8, [s + 5, s + 3, 2*s + 2, s + 3, 5, s + 3, s + 2], rfl, by omega, by omega, ?_,
    by simp, by simp, ?_, ?_⟩
  · intro x hx; simp at hx; omega
  · simp [valB, P7]; ring
  · simp [valB, P7]; ring

def P8 (s : ℕ) : ℕ := 2494357888*s^8 + 22449220992*s^7 + 88384788800*s^6 + 198825482768*s^5 + 279513961056*s^4 + 251462053348*s^3 + 141377247682*s^2 + 45415822799*s + 6382224601

theorem A191303_k8 (s : ℕ) : HalfPal 8 (P8 s) := by
  refine ⟨22*s + 24, 22*s + 25, [s + 1, 8*s + 9, 8*s + 9, 11*s + 12, 12*s + 13, 3*s + 3, s + 1, s + 1], rfl, by omega, by omega, ?_,
    by simp, by simp, ?_, ?_⟩
  · intro x hx; simp at hx; omega
  · simp [valB, P8]; ring
  · simp [valB, P8]; ring

def P9 (s : ℕ) : ℕ := 25600000000*s^9 + 719360000000*s^8 + 8981504000000*s^7 + 65395008000000*s^6 + 306004200800000*s^5 + 954307631056000*s^4 + 1983463230084000*s^3 + 2649334279001480*s^2 + 2063596203662541*s + 714142247103938

theorem A191303_k9 (s : ℕ) : HalfPal 9 (P9 s) := by
  refine ⟨20*s + 63, 20*s + 64, [s + 2, 18*s + 55, 6*s + 18, 18*s + 61, 15*s + 50, 4*s + 8, 8*s + 24, 10*s + 34, s + 2], rfl, by omega, by omega, ?_,
    by simp, by simp, ?_, ?_⟩
  · intro x hx; simp at hx; omega
  · simp [valB, P9]; ring
  · simp [valB, P9]; ring

def P10 (s : ℕ) : ℕ := 22938115138048*s^10 + 2327395548408832*s^9 + 106265629993373312*s^8 + 2875208184933144192*s^7 + 51051995091150075264*s^6 + 621579907504046041232*s^5 + 5255527946765116545624*s^4 + 30470287525167646167748*s^3 + 115932096915022225910446*s^2 + 261387410048746763846647*s + 265201372778717338121730

theorem A191303_k10 (s : ℕ) : HalfPal 10 (P10 s) := by
  refine ⟨22*s + 223, 22*s + 224, [19*s + 194, 11*s + 102, 19*s + 167, 13*s + 137, s + 58, 10*s + 100, 22*s + 183, 21*s + 222, 16*s + 175, 19*s + 186], rfl, by omega, by omega, ?_,
    by simp, by simp, ?_, ?_⟩
  · intro x hx; simp at hx; omega
  · simp [valB, P10]; ring
  · simp [valB, P10]; ring

def P11 (s : ℕ) : ℕ := 3181801204736*s^11 + 426258056200704*s^10 + 25956555718926336*s^9 + 948353745332965888*s^8 + 23099362322527977024*s^7 + 393844916925436172000*s^6 + 4796451410590939172976*s^5 + 41723852831843755756736*s^4 + 254064734737535860438776*s^3 + 1031360982754873914635646*s^2 + 2512035922068960860892111*s + 2781095483894400570527480

theorem A191303_k11 (s : ℕ) : HalfPal 11 (P11 s) := by
  refine ⟨14*s + 170, 14*s + 171, [11*s + 137, 13*s + 161, 12*s + 130, 12*s + 123, 7*s + 107, 7*s + 121, 7*s + 63, 2*s + 1, 12*s + 162, s + 15, 11*s + 130], rfl, by omega, by omega, ?_,
    by simp, by simp, ?_, ?_⟩
  · intro x hx; simp at hx; omega
  · simp [valB, P11]; ring
  · simp [valB, P11]; ring

def P13 (s : ℕ) : ℕ := 2176782336000000000000*s^13 + 45712429056000000000000*s^12 + 442939530332160000000000*s^11 + 2622128924021760000000000*s^10 + 10580535405321984000000000*s^9 + 30730181125888765440000000*s^8 + 66093072571839003840000000*s^7 + 106578758832360179616000000*s^6 + 128855969736078604377600000*s^5 + 115360620337052943537600000*s^4 + 74334560768850022037550000*s^3 + 32646351829021687227536640*s^2 + 8758604885767714845539341*s + 1084109387961191247324901

theorem A191303_k13 (s : ℕ) : HalfPal 13 (P13 s) := by
  refine ⟨60*s + 98, 60*s + 99, [s + 1, 24*s + 37, 25*s + 38, 10*s + 20, 30*s + 60, 18*s + 27, 27*s + 29, 6*s + 12, 11, 20*s + 29, 7*s + 8, 12*s + 22, s + 1], rfl, by omega, by omega, ?_,
    by simp, by simp, ?_, ?_⟩
  · intro x hx; simp at hx; omega
  · simp [valB, P13]; ring
  · simp [valB, P13]; ring

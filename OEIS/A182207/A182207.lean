/-
OEIS A182207. Conjecture (Coman): every Carmichael number C divisible by p and
2p - 1 (both prime) is p(2p - 1)(n(2p - 2) + p), n natural. True. Carmichael
numbers are odd, so p = 2r + 1 with r ≥ 1 and 2p - 2 = 4r. Write C = p(2p-1) m.
Korselt for the prime 2p - 1 gives 4r | C - 1. Then 4r | m - p (below). Since
0 < m and p < 4r + p, m ≡ p (mod 4r) gives m = p + 4r n with n ≥ 0 (and n ≥ 1
since m = p would make p^2 | C).

Checked here (core Lean, grind): `cofactor`, for all integers r, m: if
4r | (2r+1)(4r+1)m - 1 then 4r | m - (2r+1). Witness:
m - p = 4r (p c - (4r^2 + 5r + 2) m) where p(2p-1)m - 1 = 4r c.
Not checked here: Korselt's criterion in the necessary direction (if C is a
Carmichael number and p is a prime factor then p - 1 | C - 1, and C is
squarefree), which needs Fermat's little theorem and a primitive root mod p.
-/

theorem cofactor (r m : Int) (h : (4 * r) ∣ ((2 * r + 1) * (4 * r + 1) * m - 1)) :
    (4 * r) ∣ (m - (2 * r + 1)) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨(2 * r + 1) * c - (4 * r * r + 5 * r + 2) * m, by grind⟩

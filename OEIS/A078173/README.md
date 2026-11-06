# OEIS A078173: max t = n(n+2) and max s = 2n over solutions of rst = n(r+s+t)

**Source.** OEIS [A078173](https://oeis.org/A078173) (John W. Layman, Nov 20 2002): a(n) = max(min(r,s,t)) over
positive integer solutions of r*s*t = n*(r+s+t). Comment: "Conjecture: max(t) = n*(n+2) and max(s) = 2*n,"
maxima over all positive integer solutions r <= s <= t. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True for every n >= 1.

**Argument.** Let r <= s <= t be positive with rst = n(r+s+t). Then t(rs - n) = n(r+s) > 0, so d = rs - n >= 1.
- *max t.* If r = 1 the equation is (s - n)(t - n) = n(n+1) with s - n >= 1, so t <= n + n(n+1) = n(n+2).
  If r >= 2 then (r-2)(s-2) >= 0 gives 2(r+s) <= rs + 4 = n + d + 4, so 2td <= n(n+d+4). If t >= n(n+2)+1
  this gives d(2n^2 + 3n + 2) <= n^2 + 4n, impossible for d >= 1 as n^2 - n + 2 > 0.
  Attained by (1, n+1, n(n+2)).
- *max s.* From t >= s, s(rs - n) <= t(rs - n) = n(r+s), so s(rs - 2n) <= nr. If s >= 2n+1 then
  rs - 2n >= r(2n+1) - 2n >= r, so s(rs - 2n) >= (2n+1)r > nr. Hence s <= 2n, attained by (1, 2n, 2n+1).

**Evidence.**
- Lean (Mathlib): [`A078173_mathlib.lean`](A078173_mathlib.lean). `A078173_max_t : 1 ≤ n → IsGreatest {t | ∃ r s,
  Sol n r s t} (n*(n+2))` and `A078173_max_s : 1 ≤ n → IsGreatest {s | ∃ r t, Sol n r s t} (2*n)`, where
  `Sol n r s t` is 0 < r ≤ s ≤ t ∧ r*s*t = n*(r+s+t) in ℕ. Checked with `tools/leancheck-mathlib.sh`, no warnings;
  axioms propext, Classical.choice, Quot.sound.
- [`certificate/brute.py`](certificate/brute.py): all solutions for n = 1..40 (using rs <= 3n), confirms both maxima.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: the entry carries the claim as an unattributed conjecture with no proof; not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones of 2026-11-05). The bound is a short
Egyptian-fraction-type argument; no published proof found.

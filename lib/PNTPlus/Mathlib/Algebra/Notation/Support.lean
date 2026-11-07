-- Vendored from github.com/AlexKontorovich/PrimeNumberTheoremAnd, rev 127b50e3,
-- file PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean (Apache-2.0, see lib/PNTPlus/README.md).
-- Modified: LeanArchitect blueprint metadata removed, imports renamed to PNTPlus.*
--
import Mathlib.Algebra.Notation.Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

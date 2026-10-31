module

public import Mathlib.Algebra.Notation.Support

/-!
Adapted from AlexKontorovich/PrimeNumberTheoremAnd, PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean,
commit 127b50e33f6033e2147921167a117af96d9ba4ea, Git blob 13d3575b14d663481b15e0099f75c42739668f40,
Apache-2.0. Scope: two support identities.
Changes: P1 namespaces and Lean 4.36 module/public declarations.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PNT.SupportHelpers

open Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end PaperP1.PNT.SupportHelpers

module

public import PaperP1.Algebra.FinitePiExtension

/-! # Extension by zero is injective and vanishes off the actual embedding -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePiExtensionSupport

open Finset

variable {K ι κ : Type*} [DivisionRing K] [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem extend_injective (e : ι ↪ κ) : Function.Injective (FinitePiExtension.extend (K := K) e) := by
  intro w v he
  funext i
  have hh := congrFun he (e i)
  simpa only [FinitePiExtension.extend_at] using hh

omit [Fintype κ] in
theorem extend_zero_outside (e : ι ↪ κ) (w : ι → K) (j : κ) (hj : ∀ i, e i ≠ j) :
    FinitePiExtension.extend e w j = 0 := by
  classical
  rw [FinitePiExtension.extend_apply, Finset.sum_apply]
  apply sum_eq_zero
  intro i _
  simp [(hj i).symm]

end PaperP1.FinitePiExtensionSupport

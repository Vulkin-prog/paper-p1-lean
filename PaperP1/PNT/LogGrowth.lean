module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Adapted from AlexKontorovich/PrimeNumberTheoremAnd, PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean,
commit 127b50e33f6033e2147921167a117af96d9ba4ea, Git blob 1fa2d2b6a88a2b891dc7674914e8e3fa7d19472c,
Apache-2.0. Scope: the proved logarithmic-power limit.
Changes: P1 namespace, Lean 4.36 module/public declarations,
obsolete natural-cast helpers replaced by current Mathlib theorems.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PNT

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end PaperP1.PNT

module

public import PaperP1.Analysis.DeterminantShapeStability
public import PaperP1.Analysis.ReducedSourceLogarithms

/-! # Compare every reduced determinant exponential with its original source-box value -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedDeterminantShape

open PaperP1.DeterminantSourceBox PaperP1.ReducedDyadicScales PaperP1.ReducedSourceParameter
open PaperP1.DeterminantLogScale PaperP1.DeterminantShapeStability

theorem uniform_exp_comparison (C K A η : ℝ) (hC : 0 < C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℕ, 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ, ∀ g q : ℕ, 0 < g → 0 < q → g ^ 2 * q ≤ h →
      Real.exp (logShape (parameter N (g ^ 2 * q))
          (enlarged X.D g) (enlarged X.E g) (enlarged X.U q) (enlarged X.V q)) ≤
        (N : ℝ) ^ η * Real.exp (logShape N X.D X.E X.U X.V) := by
  obtain ⟨Nb, hb⟩ := DeterminantBoxScales.uniform_base_logs C hC
  obtain ⟨Nm, hm⟩ := ReducedSourceLogarithms.uniform_shift_margin K A (16 * η / 81) (by positivity)
  refine ⟨max 1 (max ⌈Real.exp (1 : ℝ)⌉₊ (max Nb Nm)), ?_⟩
  intro N hN h hh hshift ρ δ X g q hg hq hscale
  have hn₁ : 1 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hexp : Real.exp (1 : ℝ) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp (1 : ℝ)⌉₊ ≤ N by omega))
  have ht : 1 ≤ Real.log (N : ℝ) := by
    have hlog := Real.log_le_log (Real.exp_pos (1 : ℝ)) hexp
    simpa only [Real.log_exp] using hlog
  obtain ⟨_hN₂, hAu, hBu⟩ := hb N (by omega) X.c₁ X.c₂ X.D X.E X.U X.V
    X.c₁_ge_one X.c₂_ge_one X.D_ge_one X.E_ge_one X.U_ge_one X.V_ge_one X.first_upper X.second_upper
  obtain ⟨_hN₁, hroot, hsmall⟩ := hm N (by omega) h hh hshift
  have hs : 0 < g ^ 2 * q := Nat.mul_pos (pow_pos hg 2) hq
  have hhalf := parameter_log_lower N (g ^ 2 * q) h (by omega) hs hscale hroot
  have hle := parameter_log_upper N (g ^ 2 * q) (by omega) hs
  have hgap : Real.log N - Real.log (parameter N (g ^ 2 * q)) ≤ Real.log h :=
    (log_parameter_gap N (g ^ 2 * q) (by omega) hs).trans
      (Real.log_le_log (by exact_mod_cast hs : (0 : ℝ) < (g ^ 2 * q : ℕ)) (by exact_mod_cast hscale))
  have hA₀ : 0 ≤ Real.log (X.D * X.E) := by
    apply Real.log_nonneg
    nlinarith only [X.D_ge_one, X.E_ge_one, mul_nonneg (sub_nonneg.mpr X.D_ge_one) (sub_nonneg.mpr X.E_ge_one)]
  have hB₀ : 0 ≤ Real.log (X.U * X.V) := by
    apply Real.log_nonneg
    nlinarith only [X.U_ge_one, X.V_ge_one, mul_nonneg (sub_nonneg.mpr X.U_ge_one) (sub_nonneg.mpr X.V_ge_one)]
  have hde := enlarged_log_bounds X.D X.E g X.D_ge_one X.E_ge_one hg
  have huv := enlarged_log_bounds X.U X.V q X.U_ge_one X.V_ge_one hq
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ h by omega))
  have hweighted := weighted_loss (Real.log N) (Real.log (parameter N (g ^ 2 * q)))
    (Real.log (X.D * X.E)) (Real.log (X.U * X.V))
    (Real.log (enlarged X.D g * enlarged X.E g)) (Real.log (enlarged X.U q * enlarged X.V q))
    0 (Real.log h) ht hhalf hle hA₀ hB₀ hAu hBu hde.1 huv.1 (by norm_num)
    (by simpa only [add_zero] using hde.2) (by simpa only [add_zero] using huv.2) hlogh hgap
  have hshape : logShape (parameter N (g ^ 2 * q)) (enlarged X.D g) (enlarged X.E g)
      (enlarged X.U q) (enlarged X.V q) ≤ logShape N X.D X.E X.U X.V + η * Real.log N := by
    dsimp only [logShape]
    norm_num only [mul_zero, zero_pow (by omega : 2 ≠ 0), add_zero] at hweighted
    linarith only [hweighted, hsmall]
  have hexpbound := Real.exp_le_exp.mpr hshape
  rw [Real.exp_add] at hexpbound
  have hpower : Real.exp (η * Real.log N) = (N : ℝ) ^ η := by
    rw [Real.rpow_def_of_pos hn]
    congr 1
    ring
  rw [hpower] at hexpbound
  simpa only [mul_comm] using hexpbound

end PaperP1.ReducedDeterminantShape

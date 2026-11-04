module

public import PaperP1.Arithmetic.InitialDyadicSourceBox
public import PaperP1.Analysis.ReducedDeterminantCosts

/-! # Compare the normalized initial determinant exponential and both original costs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InitialDeterminantShape

open PaperP1.InitialDyadicSourceBox PaperP1.ReducedDyadicScales
open PaperP1.DeterminantLogScale PaperP1.DeterminantShapeStability

theorem uniform_exp_comparison (C η : ℝ) (hC : 0 < C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ δ : ℝ, 0 ≤ δ → ∀ X : Box N ρ C δ,
      ∀ hhalf : 1 / 2 ≤ X.D ∧ 1 / 2 ≤ X.E ∧ 1 / 2 ≤ X.U ∧ 1 / 2 ≤ X.V,
      let Y := normalize X hhalf
      Real.exp (logShape N Y.D Y.E Y.U Y.V) ≤ (N : ℝ) ^ η * Real.exp (logShape N X.D X.E X.U X.V) := by
  let c := Real.log (4 : ℝ)
  let T := (27 / 2 : ℝ) * c + (9 / 4 : ℝ) * c ^ 2
  obtain ⟨Nb, hb⟩ := DeterminantBoxScales.uniform_base_logs (8 * C) (by positivity)
  obtain ⟨Nk, hk⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (Real.exp T) 0 η hη
  refine ⟨max 1 (max ⌈Real.exp (1 : ℝ)⌉₊ (max Nb Nk)), ?_⟩
  intro N hN ρ δ hδ X hhalf
  let Y := normalize X hhalf
  have hexp : Real.exp (1 : ℝ) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp (1 : ℝ)⌉₊ ≤ N by omega))
  have ht : 1 ≤ Real.log (N : ℝ) := by
    have hl := Real.log_le_log (Real.exp_pos (1 : ℝ)) hexp
    simpa only [Real.log_exp] using hl
  have hc : 0 ≤ c := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have hDElo := log_product_lower X.D X.E 1 X.D_pos X.E_pos (by decide)
  have hUVlo := log_product_lower X.U X.V 1 X.U_pos X.V_pos (by decide)
  simp only [Nat.cast_one, Real.log_one, mul_zero, sub_zero] at hDElo hUVlo
  change Real.log (X.D * X.E) ≤ Real.log (Y.D * Y.E) at hDElo
  change Real.log (X.U * X.V) ≤ Real.log (Y.U * Y.V) at hUVlo
  have hDEhi := log_product_upper X.D X.E 1 X.D_pos X.E_pos (by decide)
    (by simpa only [Nat.cast_one, div_one] using hhalf.1)
    (by simpa only [Nat.cast_one, div_one] using hhalf.2.1)
  have hUVhi := log_product_upper X.U X.V 1 X.U_pos X.V_pos (by decide)
    (by simpa only [Nat.cast_one, div_one] using hhalf.2.2.1)
    (by simpa only [Nat.cast_one, div_one] using hhalf.2.2.2)
  simp only [Nat.cast_one, Real.log_one, mul_zero, sub_zero] at hDEhi hUVhi
  change Real.log (Y.D * Y.E) ≤ Real.log (X.D * X.E) + c at hDEhi
  change Real.log (Y.U * Y.V) ≤ Real.log (X.U * X.V) + c at hUVhi
  obtain ⟨_hN₂, hAu, hBu⟩ := hb N (by omega) Y.c₁ Y.c₂ Y.D Y.E Y.U Y.V
    Y.c₁_ge_one Y.c₂_ge_one Y.D_ge_one Y.E_ge_one Y.U_ge_one Y.V_ge_one Y.first_upper Y.second_upper
  have hA : 0 ≤ Real.log (X.D * X.E) := (mul_nonneg hδ (by linarith : 0 ≤ Real.log N)).trans X.first_log
  have hB : 0 ≤ Real.log (X.U * X.V) := (mul_nonneg hδ (by linarith : 0 ≤ Real.log N)).trans X.second_log
  have hweighted := weighted_loss (Real.log N) (Real.log N)
    (Real.log (X.D * X.E)) (Real.log (X.U * X.V)) (Real.log (Y.D * Y.E)) (Real.log (Y.U * Y.V)) c 0
    ht (by linarith) le_rfl hA hB (hDElo.trans hAu) (hUVlo.trans hBu)
    (hA.trans hDElo) (hB.trans hUVlo) hc hDEhi hUVhi (by norm_num) (by simp only [sub_self, le_refl])
  have hshape : logShape N Y.D Y.E Y.U Y.V ≤ logShape N X.D X.E X.U X.V + T := by
    dsimp only [logShape, T]
    norm_num only [mul_zero, add_zero] at hweighted
    linarith only [hweighted]
  have hconstant : Real.exp T ≤ (N : ℝ) ^ η := by
    simpa only [Real.rpow_zero, mul_one] using hk N (by omega)
  have he := Real.exp_le_exp.mpr hshape
  rw [Real.exp_add] at he
  calc
    _ ≤ Real.exp (logShape N X.D X.E X.U X.V) * Real.exp T := he
    _ ≤ Real.exp (logShape N X.D X.E X.U X.V) * (N : ℝ) ^ η :=
      mul_le_mul_of_nonneg_left hconstant (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

theorem uniform_cost_comparison (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ δ : ℝ, 0 ≤ δ → ∀ X : Box N ρ C δ,
      ∀ hhalf : 1 / 2 ≤ X.D ∧ 1 / 2 ≤ X.E ∧ 1 / 2 ≤ X.U ∧ 1 / 2 ≤ X.V,
      let Y := normalize X hhalf
      let F' := Real.exp (logShape N Y.D Y.E Y.U Y.V)
      let F := Real.exp (logShape N X.D X.E X.U X.V)
      Real.sqrt (Y.D * Y.E * F') + Y.D + Y.E ≤ (N : ℝ) ^ ε * (Real.sqrt (X.D * X.E * F) + X.D + X.E) ∧
        Real.sqrt (Y.U * Y.V * F') + Y.U + Y.V ≤ (N : ℝ) ^ ε * (Real.sqrt (X.U * X.V * F) + X.U + X.V) := by
  obtain ⟨Ns, hs⟩ := uniform_exp_comparison C ε hC hε
  obtain ⟨Nk, hk⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow 2 0 (ε / 2) (by positivity)
  refine ⟨max 1 (max Ns Nk), ?_⟩
  intro N hN ρ δ hδ X hhalf
  let Y := normalize X hhalf
  let F' := Real.exp (logShape N Y.D Y.E Y.U Y.V)
  let F := Real.exp (logShape N X.D X.E X.U X.V)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR := Real.one_le_rpow hn₁ (show 0 ≤ ε / 2 by positivity)
  have hpower : (N : ℝ) ^ ε = ((N : ℝ) ^ (ε / 2)) ^ 2 := by
    calc
      _ = (N : ℝ) ^ ((ε / 2) * 2) := by congr 1; ring
      _ = _ := by rw [Real.rpow_mul hn.le, Real.rpow_two]
  have hf : F' ≤ ((N : ℝ) ^ (ε / 2)) ^ 2 * F := by
    rw [← hpower]
    exact hs N (by omega) ρ δ hδ X hhalf
  have htwo : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by simpa only [Real.rpow_zero, mul_one] using hk N (by omega)
  have hpref : 2 * (N : ℝ) ^ (ε / 2) ≤ (N : ℝ) ^ ε := by
    rw [hpower, pow_two]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hn.le _)
  have hd : Y.D ≤ 2 * X.D := by
    change enlarged X.D 1 ≤ 2 * X.D
    simpa only [Nat.cast_one, div_one] using enlarged_le_double X.D 1 (by simpa only [Nat.cast_one, div_one] using hhalf.1)
  have he : Y.E ≤ 2 * X.E := by
    change enlarged X.E 1 ≤ 2 * X.E
    simpa only [Nat.cast_one, div_one] using enlarged_le_double X.E 1 (by simpa only [Nat.cast_one, div_one] using hhalf.2.1)
  have hu : Y.U ≤ 2 * X.U := by
    change enlarged X.U 1 ≤ 2 * X.U
    simpa only [Nat.cast_one, div_one] using enlarged_le_double X.U 1 (by simpa only [Nat.cast_one, div_one] using hhalf.2.2.1)
  have hv : Y.V ≤ 2 * X.V := by
    change enlarged X.V 1 ≤ 2 * X.V
    simpa only [Nat.cast_one, div_one] using enlarged_le_double X.V 1 (by simpa only [Nat.cast_one, div_one] using hhalf.2.2.2)
  constructor
  · have hc := ReducedDeterminantCosts.pair_cost_inflation X.D X.E Y.D Y.E F F' 2 ((N : ℝ) ^ (ε / 2))
      X.D_pos.le X.E_pos.le (by linarith [Y.D_ge_one]) (by linarith [Y.E_ge_one])
      (Real.exp_nonneg _) (Real.exp_nonneg _) (by norm_num) hR hd he hf
    have hbase : 0 ≤ Real.sqrt (X.D * X.E * F) + X.D + X.E := by
      have hd₀ := X.D_pos.le
      have he₀ := X.E_pos.le
      positivity
    exact hc.trans (mul_le_mul_of_nonneg_right hpref hbase)
  · have hc := ReducedDeterminantCosts.pair_cost_inflation X.U X.V Y.U Y.V F F' 2 ((N : ℝ) ^ (ε / 2))
      X.U_pos.le X.V_pos.le (by linarith [Y.U_ge_one]) (by linarith [Y.V_ge_one])
      (Real.exp_nonneg _) (Real.exp_nonneg _) (by norm_num) hR hu hv hf
    have hbase : 0 ≤ Real.sqrt (X.U * X.V * F) + X.U + X.V := by
      have hu₀ := X.U_pos.le
      have hv₀ := X.V_pos.le
      positivity
    exact hc.trans (mul_le_mul_of_nonneg_right hpref hbase)

end PaperP1.InitialDeterminantShape

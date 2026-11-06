module

public import PaperP1.Analysis.LogarithmicWindowCells


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LogarithmicCellSquareBudget
open Finset MeasureTheory PaperP1 LogarithmicWindowCells
open scoped Classical

theorem cell_lower (G : ℝ → ℝ) (hG : Integrable (fun u ↦ (G u)^2)) (κ c : ℝ) (j : ℕ)
    (hκ : 0 ≤ κ) (hLower : ∀ u ∈ cell c j, κ ≤ |G u|) :
    κ^2*volume.real (cell c j) ≤ ∫ u in cell c j, (G u)^2 := by
  have hConst : IntegrableOn (fun _u : ℝ ↦ κ^2) (cell c j) volume := by
    have hh : IntegrableOn (fun _u : ℝ ↦ κ^2)
        (Set.Icc (-Real.log ((j : ℝ)+c+1)) (-Real.log ((j : ℝ)+c))) volume :=
      continuous_const.integrableOn_Icc
    exact hh.mono_set Set.Ioc_subset_Icc_self
  have hBound : (∫ _u in cell c j, κ^2) ≤ ∫ u in cell c j, (G u)^2 := by
    apply integral_mono_ae hConst hG.integrableOn
    filter_upwards [ae_restrict_mem (cell_measurable c j)] with u hu
    have hh := pow_le_pow_left₀ hκ (hLower u hu) 2
    simpa only [sq_abs] using hh
  rw [setIntegral_const] at hBound
  simpa only [smul_eq_mul,mul_comm] using hBound

theorem finite_budget (B : Finset ℕ) (G : ℝ → ℝ) (hG : Integrable (fun u ↦ (G u)^2))
    (κ c M : ℝ) (hκ : 0 ≤ κ) (hX : ∀ j ∈ B, 0 < (j : ℝ)+c)
    (hTop : ∀ j ∈ B, (j : ℝ)+c+1 ≤ M)
    (hLower : ∀ j ∈ B, ∀ u ∈ cell c j, κ ≤ |G u|) :
    (B.card : ℝ)*κ^2/M ≤ ∫ u : ℝ, (G u)^2 := by
  have hEach (j : ℕ) (hj : j ∈ B) : κ^2/M ≤ ∫ u in cell c j, (G u)^2 := by
    calc
      _ = κ^2*(1/M) := by ring
      _ ≤ κ^2*volume.real (cell c j) :=
        mul_le_mul_of_nonneg_left (cell_measure_lower c M j (hX j hj) (hTop j hj)) (sq_nonneg κ)
      _ ≤ _ := cell_lower G hG κ c j hκ (hLower j hj)
  have hDisjoint : Set.PairwiseDisjoint (B : Set ℕ) (cell c) := by
    intro i hi j hj hij
    exact cells_disjoint c i j (hX i hi) (hX j hj) hij
  have hUnion := integral_biUnion_finset B (fun j hj ↦ cell_measurable c j)
    hDisjoint (fun j hj ↦ hG.integrableOn)
  have hWhole : (∫ u in ⋃ j ∈ B, cell c j, (G u)^2) ≤ ∫ u : ℝ, (G u)^2 :=
    setIntegral_le_integral hG (Filter.Eventually.of_forall (fun u ↦ sq_nonneg _))
  rw [hUnion] at hWhole
  calc
    _ = ∑ _j ∈ B, κ^2/M := by rw [sum_const,nsmul_eq_mul]; ring
    _ ≤ ∑ j ∈ B, ∫ u in cell c j, (G u)^2 := sum_le_sum hEach
    _ ≤ _ := hWhole

end PaperP1.LogarithmicCellSquareBudget

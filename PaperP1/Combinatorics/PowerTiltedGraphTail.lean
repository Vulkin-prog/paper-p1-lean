module

public import PaperP1.Combinatorics.MarkedGraphGenerator

/-! # A uniform cardinality tilt for actual marked saturation families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PowerTiltedGraphTail

open Finset PaperP1.GraphStarWeights PaperP1.MarkedGraphGenerator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem tilt_bound (marks : Finset V) (F : Finset (Finset V)) (s : ℕ)
    (hF : F ⊆ families G marks) (hcard : ∀ D ∈ F, s ≤ D.card)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 1 ≤ T) :
    T ^ s * (∑ D ∈ F, a ^ D.card) ≤ total G marks (a * T) := by
  calc
    _ = ∑ D ∈ F, T ^ s * a ^ D.card := mul_sum _ _ _
    _ ≤ ∑ D ∈ F, (a * T) ^ D.card := by
      apply sum_le_sum
      intro D hD
      calc
        _ ≤ T ^ D.card * a ^ D.card :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT (hcard D hD)) (pow_nonneg ha _)
        _ = _ := by rw [mul_pow]; ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hF (fun D _ _ ↦ pow_nonneg (by positivity) _)

theorem total_bound (marks : Finset V) (z M : ℝ) (hz : 0 ≤ z)
    (hmark : (marks.card : ℝ) * z ≤ M)
    (hstar : (Fintype.card V : ℝ) * G.maxDegree * z ^ 2 ≤ M ^ 2)
    (hsmall : (G.maxDegree : ℝ) * z ≤ 1 / 8) :
    total G marks z ≤ Real.exp (M + 8 * M ^ 2) := by
  have hden : 0 < 1 - 4 * (G.maxDegree : ℝ) * z := by nlinarith only [hsmall]
  have hfrac : 4 * (Fintype.card V : ℝ) * G.maxDegree * z ^ 2 /
      (1 - 4 * (G.maxDegree : ℝ) * z) ≤ 8 * M ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    have hs : (1 / 2 : ℝ) ≤ 1 - 4 * (G.maxDegree : ℝ) * z := by nlinarith only [hsmall]
    have hprod := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 8 * M ^ 2)
    nlinarith only [hstar, hprod]
  exact (main_7_4 G marks z hz (by nlinarith only [hsmall])).trans
    (Real.exp_le_exp.mpr (add_le_add hmark hfrac))

end PaperP1.PowerTiltedGraphTail

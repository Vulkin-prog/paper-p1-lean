module

public import PaperP1.Asymptotics.CoupledPrincipalEdgesCount
public import PaperP1.Asymptotics.PrincipalEdgeProbability

/-! # The actual independent product weights of every coupled principal-edge pair cost N^(-7/3+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoupledPrincipalProductMass

open Finset PaperP1.Model.InfiniteStarts PaperP1.PrincipalEdgeSpaces

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → coupledProductMass N H L ≤ (N : ℝ) ^ (-7 / 3 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := CoupledPrincipalEdgesCount.uniform_count C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := PrincipalEdgeProbability.uniform_coarse C (ε / 4) (by positivity)
  refine ⟨max 10 (max NC NP), by omega, ?_⟩
  intro N hN L H hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint (p : Finset ℕ × Finset ℕ) (hp' : p ∈ coupledPairs N H L) :
      infiniteJointMoment L p.1 * infiniteJointMoment L p.2 ≤ (N : ℝ) ^ (-10 / 3 + ε / 2) := by
    obtain ⟨he, hf⟩ := mem_product.mp (mem_filter.mp hp').1
    calc
      _ ≤ (N : ℝ) ^ (-5 / 3 + ε / 4) * (N : ℝ) ^ (-5 / 3 + ε / 4) :=
        mul_le_mul (hp N (by omega) L H hband p.1 he) (hp N (by omega) L H hband p.2 hf)
          (infiniteJointMoment_nonneg L p.2) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  calc
    _ ≤ ∑ _p ∈ coupledPairs N H L, (N : ℝ) ^ (-10 / 3 + ε / 2) := sum_le_sum hpoint
    _ = ((coupledPairs N H L).card : ℝ) * (N : ℝ) ^ (-10 / 3 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 + ε / 2) * (N : ℝ) ^ (-10 / 3 + ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L H hband) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.CoupledPrincipalProductMass

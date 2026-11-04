module

public import PaperP1.Asymptotics.PositionalRestorationRates

/-! # Summed absolute original marginal bias on every dyadic subground -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NominalMarginalBias

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RegularStarts

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ x ∈ G, |infiniteMarginal x L - (2 ^ L : ℝ)⁻¹|) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NR, hr⟩ := RegularSetAsymptotic.dyadic_critical_relation_rank_le_one C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨ND, _hND, hd⟩ := PositionalRestorationRates.nominal_discarded_mass C ε hε
  refine ⟨3 + NR + NG + ND, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hfinite := RegularAffineBounds.sum_affine_deviations_le (by omega) hL
    (hr N (by omega) L hband) G hG (fun _ ↦ startRhs L)
  have hbound : (∑ x ∈ G, |infiniteMarginal x L - (2 ^ L : ℝ)⁻¹|) ≤
      (2 ^ L : ℝ)⁻¹ * (RegularStarts.irregularStarts N L).card := by
    simpa only [RegularAffineBounds.affineWindowMass, infiniteMarginal_eq_affine_atom hL] using hfinite
  apply hbound.trans
  convert hd N (by omega) L hband using 1
  rw [sum_const, nsmul_eq_mul]
  ring

end PaperP1.NominalMarginalBias

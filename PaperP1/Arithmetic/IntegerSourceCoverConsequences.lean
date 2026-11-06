module

public import PaperP1.Arithmetic.OriginalIntegerSourceCover
public import PaperP1.Arithmetic.SourceSurfaceCoverFromExactDegree

/-! # The original manuscript source-cover interface follows unconditionally from the exact integer-source cover -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerSourceCoverConsequences
open PaperP1
theorem system_cover (kmax K D : ℕ) :
    UniformSourceSurfaceCover.UniformCover kmax K D := by
  have h := OriginalIntegerSourceCover.uniform_cover kmax D
  intro δ hδ
  obtain ⟨B, C, hC, hcover⟩ := h δ hδ
  refine ⟨B, C, hC, ?_⟩
  intro s hlen d I J hs hdeg hD hd hI hJ hIne _hJne _hK H hH U hU
  obtain ⟨V, curves, _hV, hdegrees, hVbound, hcount, hpoint⟩ :=
    hcover hD s.length hlen s rfl d I J hs hdeg hd (fun i ↦ Or.inl (hIne i)) hI hJ H hH U hU
  refine ⟨V, curves, hdegrees, ?_, ?_, hpoint⟩
  · have hdecay := SourceSurfaceCoverFromExactDegree.decay_le s.length D hD
    have htwo : 2 / Real.sqrt ((2 ^ s.length * D ^ 2 : ℕ) : ℝ) ≤
        2 / Real.sqrt ((2 : ℝ) ^ s.length) := by
      simpa only [one_div, div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hdecay (by norm_num : (0 : ℝ) ≤ 2)
    have hpower := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hH : (1 : ℝ) ≤ H)
      (by linarith [htwo] : 2 / Real.sqrt ((2 ^ s.length * D ^ 2 : ℕ) : ℝ) + δ ≤
        2 / Real.sqrt ((2 : ℝ) ^ s.length) + δ)
    exact hVbound.trans (mul_le_mul_of_nonneg_left hpower hC.le)
  · have hdecay := SourceSurfaceCoverFromExactDegree.decay_le s.length D hD
    have hpower := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hH : (1 : ℝ) ≤ H)
      (by linarith [hdecay] : 1 / Real.sqrt ((2 ^ s.length * D ^ 2 : ℕ) : ℝ) + δ ≤
        1 / Real.sqrt ((2 : ℝ) ^ s.length) + δ)
    exact hcount.trans (mul_le_mul_of_nonneg_left hpower hC.le)

end IntegerSourceCoverConsequences

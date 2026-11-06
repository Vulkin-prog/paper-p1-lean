module

public import PaperP1.Arithmetic.UniformExactSourceCoverFromP3
public import PaperP1.Arithmetic.UniformSourceSurfaceCover

/-! # The manuscript source-cover interface follows from the full genuine-degree cover without changing its actual curves or points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfaceCoverFromExactDegree

theorem decay_le (k D : ℕ) (hD : 0 < D) :
    1 / Real.sqrt ((2 ^ k * D ^ 2 : ℕ) : ℝ) ≤ 1 / Real.sqrt ((2 : ℝ) ^ k) := by
  apply one_div_le_one_div_of_le (by positivity)
  apply Real.sqrt_le_sqrt
  have hD' : 1 ≤ D ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hD))
  have hh : (2 ^ k : ℕ) ≤ 2 ^ k * D ^ 2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ k) hD'
  exact_mod_cast hh

theorem of_exact {kmax K D : ℕ} (h : ExactDegreeSourceSurfaceCover.UniformCover kmax D) :
    UniformSourceSurfaceCover.UniformCover kmax K D := by
  intro δ hδ
  obtain ⟨B, C, hC, hcover⟩ := h δ hδ
  refine ⟨B, C, hC, ?_⟩
  intro s hlen d I J hs hdeg hD hd hI hJ hIne _hJne _hK H hH U hU
  obtain ⟨V, curves, _hV, hdegrees, hVbound, hcount, hpoint⟩ :=
    hcover hD s.length hlen s rfl (fun i ↦ (d i : ℚ)) I J hs hdeg
      (fun i ↦ Int.cast_ne_zero.mpr (hd i)) (fun i ↦ Or.inl (hIne i)) hI hJ H hH U hU
  refine ⟨V, curves, hdegrees, ?_, ?_, hpoint⟩
  · have hdecay := decay_le s.length D hD
    have htwo : 2 / Real.sqrt ((2 ^ s.length * D ^ 2 : ℕ) : ℝ) ≤
        2 / Real.sqrt ((2 : ℝ) ^ s.length) := by
      simpa only [one_div, div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hdecay (by norm_num : (0 : ℝ) ≤ 2)
    have hpower := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hH : (1 : ℝ) ≤ H)
      (by linarith [htwo] : 2 / Real.sqrt ((2 ^ s.length * D ^ 2 : ℕ) : ℝ) + δ ≤
        2 / Real.sqrt ((2 : ℝ) ^ s.length) + δ)
    exact hVbound.trans (mul_le_mul_of_nonneg_left hpower hC.le)
  · have hdecay := decay_le s.length D hD
    have hpower := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hH : (1 : ℝ) ≤ H)
      (by linarith [hdecay] : 1 / Real.sqrt ((2 ^ s.length * D ^ 2 : ℕ) : ℝ) + δ ≤
        1 / Real.sqrt ((2 : ℝ) ^ s.length) + δ)
    exact hcount.trans (mul_le_mul_of_nonneg_left hpower hC.le)

theorem of_hypersurface_covers (kmax K D : ℕ)
    (hP3 : ∀ k : ℕ, k ≤ kmax → UniformP3HypersurfaceCover.UniformCover (2 ^ k * D ^ 2)) :
    UniformSourceSurfaceCover.UniformCover kmax K D :=
  of_exact (UniformExactSourceCoverFromP3.of_hypersurface_covers kmax D hP3)

end PaperP1.SourceSurfaceCoverFromExactDegree

module

public import PaperP1.Asymptotics.PositionalCompoundDeletionRate
public import PaperP1.Asymptotics.PositionalFullApproximation
public import PaperP1.Model.PositionalDeletedFields

/-! # The actual erased and isolated fields have the independent Poisson background

This proves the field-distance part of T19.10 using the unconditional main20.1
comparison. Its sharper intensity, covariance and two-edge conclusions are separate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalOriginalDeletion

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CompletedPositionalLaw
  PaperP1.PositionalDeletedFields PaperP1.PositionalDeletionKernels
  PaperP1.RetainedComponentActivity

theorem uniform_norm_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
        let U := PositionalMarkedPairExpansion.background (dyadicBlock N) E
          (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
        ‖onceLaw E (dyadicBlock N) L - U‖ ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
        ‖isolatedLaw E (dyadicBlock N) L - U‖ ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := PositionalFullApproximation.uniform_norm_bound C (ε / 2) (by positivity)
  obtain ⟨ND, _hND, hd⟩ := PositionalCompoundDeletionRate.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + ND + NF + NA, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
  let A := original (dyadicBlock N) L
  let T := PositionalCompoundPoisson.target (dyadicBlock N) E
    (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
  let U := PositionalMarkedPairExpansion.background (dyadicBlock N) E
    (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
  let P := (N : ℝ) ^ (-4 / 5 + ε / 2)
  have hA : ‖A - T‖ ≤ P := ha N (by omega) L hband
  have hD := hd N (by omega) L hband (8 * (L + 1) : ℕ)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ) ^ (-1 + ε / 2) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [] : (-1 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2)
  have hfactor : 2 * P ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hbound (K : Space ℕ →L[ℝ] Space ℕ)
      (hK : ‖K A - K T‖ ≤ ‖A - T‖) (hU : ‖K T - U‖ ≤ (N : ℝ) ^ (-1 + ε / 2)) :
      ‖K A - U‖ ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    have htri := norm_add_le (K A - K T) (K T - U)
    rw [sub_add_sub_cancel] at htri
    have hfirst := hK.trans hA
    have hsecond := hU.trans hpower
    linarith only [htri, hfirst, hsecond, hfactor]
  exact ⟨hbound (once E) (once_contraction E A T) hD.1,
    hbound (isolated E) (isolated_contraction E A T) hD.2⟩

end PaperP1.PositionalOriginalDeletion

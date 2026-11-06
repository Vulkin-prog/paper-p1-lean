module

public import PaperP1.Arithmetic.ExactDegreeSourceSurfaceCover

/-! # Exact genuine-degree covers restricted to the literal integer source coefficients of the paper -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerExactSourceSurfaceCover

open PaperP1 HomogeneousSplitRadicalData SourceProjectiveEmbedding SourceProjectiveCurveData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

def CoverAtSize (k D : ℕ) (hD : 0 < D) (B : ℕ) (C δ : ℝ) : Prop :=
  ∀ (s : List (PolynomialRing ℚ)), s.length = k →
  ∀ (cZ : Fin s.length → ℤ) (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (cZ i : ℚ) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D),
    (∀ i, cZ i ≠ 0) → (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
    (Pairwise fun i j ↦ Disjoint (I i) (I j)) → (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
  ∀ H : ℕ, 1 ≤ H → ∀ U : Finset (GeneratorIndex ℚ (Fin s.length) D → ℤ),
    U ⊆ SourceIntegerPoints.curvePoints D
      (RingHom.ker (SourceProjectiveEmbedding.evaluation (fun i ↦ (cZ i : ℚ)) D I J hdeg hD).toRingHom) H →
    ∃ (V : Finset (GeneratorIndex ℚ (Fin s.length) D → ℤ)) (curves : Finset (Curve s (fun i ↦ (cZ i : ℚ)) D I J hdeg hD)),
      V ⊆ U ∧ (∀ Γ ∈ curves, degree s (fun i ↦ (cZ i : ℚ)) D I J hs hdeg hD Γ ≤ (B : ℚ)) ∧
      (V.card : ℝ) ≤ C * (H : ℝ) ^ (2 / Real.sqrt ((2 ^ k * D ^ 2 : ℕ) : ℝ) + δ) ∧
      (curves.card : ℝ) ≤ C * (H : ℝ) ^ (1 / Real.sqrt ((2 ^ k * D ^ 2 : ℕ) : ℝ) + δ) ∧
      ∀ v ∈ U, v ∉ V → ∃ Γ ∈ curves,
        v ∈ SourceIntegerPoints.curvePoints D (SourceProjectiveCurveData.ideal s (fun i ↦ (cZ i : ℚ)) D I J hdeg hD Γ) H

def UniformCover (kmax D : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (B : ℕ) (C : ℝ), 0 < C ∧
    ∀ (hD : 0 < D) (k : ℕ), k ≤ kmax → CoverAtSize k D hD B C δ

theorem CoverAtSize.mono {k D B B' : ℕ} {hD : 0 < D} {C C' δ : ℝ}
    (h : CoverAtSize k D hD B C δ) (hB : B ≤ B') (hC : C ≤ C') : CoverAtSize k D hD B' C' δ := by
  intro s hlen c I J hs hdeg hc hne hI hJ H hH U hU
  obtain ⟨V, curves, hV, hdegrees, hVbound, hcount, hcover⟩ := h s hlen c I J hs hdeg hc hne hI hJ H hH U hU
  refine ⟨V, curves, hV, ?_, ?_, ?_, hcover⟩
  · intro Γ hΓ
    exact (hdegrees Γ hΓ).trans (by exact_mod_cast hB)
  · exact hVbound.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg H) _))
  · exact hcount.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg H) _))

end IntegerExactSourceSurfaceCover
